/* Qilin - a Java Pointer Analysis Framework
 * Copyright (C) 2021-2030 Qilin developers
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3.0 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 *
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <https://www.gnu.org/licenses/lgpl-3.0.en.html>.
 */
package qilin.core.solver

import com.google.common.collect.Queues
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import qilin.CoreConfig
import qilin.core.PTA
import qilin.core.PTAScene
import qilin.core.builder.CallGraphBuilder
import qilin.core.builder.ExceptionHandler
import qilin.core.graph.NoBackEdgeDirectGraph
import qilin.core.pag.*
import qilin.core.sets.ExpectedSize
import qilin.core.sets.HybridPointsToSet
import qilin.core.sets.P2SetVisitor
import qilin.core.sets.PointsToSetInternal
import qilin.util.PTAUtils
import soot.*
import soot.Unit
import soot.jimple.DynamicInvokeExpr
import soot.jimple.InstanceInvokeExpr
import soot.jimple.Stmt
import soot.jimple.ThrowStmt
import soot.jimple.spark.pag.SparkField
import soot.jimple.toolkits.callgraph.Edge
import soot.options.Options
import soot.util.queue.ChunkedQueue
import java.util.*
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.ConcurrentSkipListSet
import kotlin.collections.HashSet
import kotlin.math.max

class KSolver(pta: PTA) : Propagator() {
    @OptIn(FlowPreview::class)
    var concurrency = max(DEFAULT_CONCURRENCY, 1)

    private val valNodeWorkList = ConcurrentSkipListSet<ValNode>()
    private val pag: PAG
    private val pta: PTA
    private val cgb: CallGraphBuilder = pta.cgb
    private val eh: ExceptionHandler
    private val edgeQueue: Queue<Pair<Node, Node>>

    private val noBackEdgeGraph: NoBackEdgeDirectGraph<Node> = NoBackEdgeDirectGraph()

    init {
        edgeQueue = Queues.newConcurrentLinkedQueue()
        this.pag = pta.pag
        pag.setEdgeQueue(edgeQueue)
        this.eh = pta.exceptionHandler
        this.pta = pta
    }

    private var iterCnt = 0


    private fun process(curr: ValNode) {
        val pts = curr.p2Set
        val newSet = pts.newSet
        propagateSimpleEdge(curr, newSet)
        if (curr is VarNode) {
            // Step 1 continues.
            val throwSites = eh.throwSitesLookUp(curr)
            for (site in throwSites) {
                eh.exceptionDispatch(newSet, site)
            }
            // Step 2: Resolving Indirect Constraints.
            handleStoreAndLoadOnBase(newSet, curr)
            // Step 3: Collecting New Constraints.
            val sites = cgb.callSitesLookUp(curr) // VirtualCallSites
            val rmQueue: ChunkedQueue<MethodOrMethodContext> = ChunkedQueue()
            val rmReader = rmQueue.reader()
            for (site in sites) {
                cgb.virtualCallDispatch(newSet, site, rmQueue)
            }
            val rmp = ReachableMethodProcessor()
            rmp.processStmts(rmReader, rmQueue)
        }
        pts.flushNew()
    }

    @OptIn(FlowPreview::class)
    open fun getDispatcher(): CoroutineDispatcher {
        val dispatcher = Dispatchers.Default.let {
            if (concurrency != DEFAULT_CONCURRENCY)
                it.limitedParallelism(concurrency)
            else
                it
        }
        return dispatcher
    }

    override fun propagate() {
        val rmpInit = ReachableMethodProcessor()
        rmpInit.initReachableMethods()
        var first = true

        pag.alloc.forEach { (a: AllocNode, set: Set<VarNode>) ->
            set.forEach { v: VarNode ->
                propagatePTS(v, a)
            }
        }


        runBlocking(getDispatcher()) {
            while (valNodeWorkList.isNotEmpty()) {
                iterCnt ++

                coroutineScope {
                    while (valNodeWorkList.isNotEmpty()) {
                        val curr = checkNotNull(valNodeWorkList.pollFirst())
                        launch {
                            synchronized(curr) {
                                process(curr)
                            }
                        }
                    }
                }

                // Step 4: Activating New Constraints.
                if (first) {
                    first = false
                    rmpInit.activateConstraints()
                    rmpInit.activateExceptionConstraints()
                }

                propagateAddedEdges(edgeQueue)
            }
        }
        println("PAG: $pag iterate count: $iterCnt")
    }




    inner class ReachableMethodProcessor() {
        val virtualCallSiteQueue = ChunkedQueue<VirtualCallSite>()
        val throwSiteQueue = ChunkedQueue<ExceptionThrowSite>()
        val newVirtualCallSites = virtualCallSiteQueue.reader()
        val newThrowsSite = throwSiteQueue.reader()

        fun initReachableMethods() {
            val rmQueue: ChunkedQueue<MethodOrMethodContext> = ChunkedQueue()
            val r = rmQueue.reader()
            for (momc in cgb.entryPoints) {
                if (cgb.addReachableSites(momc)) {
                    rmQueue.add(momc)
                }
            }
            processStmts(r, rmQueue)
        }

        fun activateExceptionConstraints() {
            while (newThrowsSite.hasNext()) {
                val ets = newThrowsSite.next()
                val throwNode = ets.throwNode
                eh.exceptionDispatch(throwNode.p2Set.oldSet, ets)
            }
        }

        fun activateConstraints() {
            val rmQueue: ChunkedQueue<MethodOrMethodContext> = ChunkedQueue()
            val rmReader = rmQueue.reader()
            while (newVirtualCallSites.hasNext()) {
                while (newVirtualCallSites.hasNext()) {
                    val site = newVirtualCallSites.next()
                    val receiver = site.recNode()
                    cgb.virtualCallDispatch(receiver.p2Set.oldSet, site, rmQueue)
                }
                processStmts(rmReader, rmQueue) // may produce new calls, thus an out-loop is a must.
            }
        }

        fun processStmts(newRMs: Iterator<MethodOrMethodContext>, rmQueue: ChunkedQueue<MethodOrMethodContext>) {
            while (newRMs.hasNext()) {
                val momc = newRMs.next()
                val method = momc.method()
                if (method.isPhantom) {
                    continue
                }
                val mpag = pag.getMethodPAG(method)
                addToPAG(mpag, momc.context(), rmQueue)
                // !FIXME in a context-sensitive pointer analysis, clinits in a method maybe added multiple times.
                if (CoreConfig.v().ptaConfig.clinitMode == CoreConfig.ClinitMode.ONFLY) {
                    // add <clinit> find in the method to reachableMethods.
                    val it = mpag.triggeredClinits()
                    while (it.hasNext()) {
                        val sm = it.next()
                        cgb.injectCallEdge(sm.declaringClass.type, pta.parameterize(sm, pta.emptyContext()), Kind.CLINIT, rmQueue)
                    }
                }
                recordCallStmts(momc, mpag.invokeStmts, rmQueue)
                recordThrowStmts(momc, mpag.stmt2wrapperedTraps.keys)
            }
        }

        private fun recordCallStmts(m: MethodOrMethodContext, units: Collection<Unit>, rmQueue: ChunkedQueue<MethodOrMethodContext>) {
            for (u in units) {
                val s = u as Stmt
                if (s.containsInvokeExpr()) {
                    val ie = s.invokeExpr
                    if (ie is InstanceInvokeExpr) {
                        val receiver = ie.base as Local
                        val recNode = cgb.getReceiverVarNode(receiver, m)
                        val subSig = ie.getMethodRef().subSignature
                        val virtualCallSite = VirtualCallSite(recNode, s, m, ie, subSig, Edge.ieToKind(ie))
                        if (cgb.recordVirtualCallSite(recNode, virtualCallSite)) {
                            virtualCallSiteQueue.add(virtualCallSite)
                        }
                    } else {
                        val tgt = ie.method
                        if (tgt != null) { // static invoke or dynamic invoke
                            var recNode = pag.getMethodPAG(m.method()).nodeFactory().caseThis()
                            recNode = pta.parameterize(recNode, m.context()) as VarNode
                            if (ie is DynamicInvokeExpr) {
                                // !TODO dynamicInvoke is provided in JDK after Java 7.
                                // currently, PTA does not handle dynamicInvokeExpr.
                            } else {
                                cgb.addStaticEdge(m, s, tgt, Edge.ieToKind(ie), rmQueue)
                            }
                        } else if (!Options.v().ignore_resolution_errors()) {
                            throw InternalError(
                                "Unresolved target " + ie.method
                                        + ". Resolution error should have occured earlier."
                            )
                        }
                    }
                }
            }
        }

        private fun recordThrowStmts(m: MethodOrMethodContext, stmts: Collection<Stmt>) {
            for (stmt in stmts) {
                val sm = m.method()
                val mpag = pag.getMethodPAG(sm)
                val nodeFactory = mpag.nodeFactory()
                var src: Node?
                if (stmt.containsInvokeExpr()) {
                    src = nodeFactory.makeInvokeStmtThrowVarNode(stmt, sm)
                } else {
                    assert(stmt is ThrowStmt)
                    val ts = stmt as ThrowStmt
                    src = nodeFactory.getNode(ts.op)
                }
                val throwNode = pta.parameterize(src, m.context()) as VarNode
                val throwSite = ExceptionThrowSite(throwNode, stmt, m)
                if (eh.addThrowSite(throwNode, throwSite)) {
                    throwSiteQueue.add(throwSite)
                }
            }
        }

        private fun addToPAG(mpag: MethodPAG, cxt: Context, rmQueue: ChunkedQueue<MethodOrMethodContext>) {
            val contexts = pag.method2ContextsMap.computeIfAbsent(mpag) { k1: MethodPAG? -> HashSet() }
            if (!contexts.add(cxt)) {
                return
            }
            val reader = mpag.internalReader.clone()
            while (reader.hasNext()) {
                var from = reader.next()
                var to = reader.next()
                if (from is AllocNode) {
                    from = pta.heapAbstractor().abstractHeap(from)
                }
                if (from is AllocNode && to is GlobalVarNode) {
                    pag.addGlobalPAGEdge(from, to)
                } else {
                    from = pta.parameterize(from, cxt)
                    to = pta.parameterize(to, cxt)
                    if (from is AllocNode) {
                        handleImplicitCallToFinalizerRegister(from, rmQueue)
                    }
                    pag.addEdge(from, to)
                }
            }
        }

        // handle implicit calls to java.lang.ref.Finalizer.register by the JVM.
        // please refer to library/finalization.logic in doop.
        private fun handleImplicitCallToFinalizerRegister(heap: AllocNode, rmQueue: ChunkedQueue<MethodOrMethodContext>) {
            if (PTAUtils.supportFinalize(heap)) {
                val rm = PTAScene.v().getMethod("<java.lang.ref.Finalizer: void register(java.lang.Object)>")
                val tgtmpag = pag.getMethodPAG(rm)
                val tgtnf = tgtmpag.nodeFactory()
                var parm: Node? = tgtnf.caseParm(0)
                val calleeCtx = pta.emptyContext()
                val baseHeap = heap.base()
                parm = pta.parameterize(parm, calleeCtx)
                pag.addEdge(heap, parm)
                cgb.injectCallEdge(baseHeap, pta.parameterize(rm, calleeCtx), Kind.STATIC, rmQueue)
            }
        }
    }

    private fun handleStoreAndLoadOnBase(newSet: HybridPointsToSet, base: VarNode) {
        for (fr in base.allFieldRefs) {
            for (v in pag.storeInvLookup(fr)) {
                handleStoreEdge(newSet, fr.field, v)
            }
            for (to in pag.loadLookup(fr)) {
                handleLoadEdge(newSet, fr.field, to)
            }
        }
    }

    private fun handleStoreEdge(baseHeaps: PointsToSetInternal, field: SparkField, from: ValNode) {
        baseHeaps.forall(object : P2SetVisitor(pta) {
            public override fun visit(n: Node) {
                if (disallowStoreOrLoadOn(n as AllocNode)) {
                    return
                }
                val fvn = pag.makeFieldValNode(field)
                val oDotF = pta.parameterize(fvn, PTAUtils.plusplusOp(n)) as ValNode
                pag.addEdge(from, oDotF)
            }
        })
    }

    private fun handleLoadEdge(baseHeaps: PointsToSetInternal, field: SparkField, to: ValNode) {
        baseHeaps.forall(object : P2SetVisitor(pta) {
            public override fun visit(n: Node) {
                if (disallowStoreOrLoadOn(n as AllocNode)) {
                    return
                }
                val fvn = pag.makeFieldValNode(field)
                val oDotF = pta.parameterize(fvn, PTAUtils.plusplusOp(n)) as ValNode
                pag.addEdge(oDotF, to)
            }
        })
    }

    private fun propagateEdge(addedSrc: Node, addedTgt: Node) {
        if (addedSrc is VarNode && addedTgt is VarNode || addedSrc is ContextField || addedTgt is ContextField) {
            // x = y; x = o.f; o.f = y;
            val srcv = addedSrc as ValNode
            val tgtv = addedTgt as ValNode
            propagatePTS(tgtv, srcv.p2Set.oldSet)
        } else if (addedSrc is FieldRefNode) { // b = a.f
            handleLoadEdge(addedSrc.base.p2Set.oldSet, addedSrc.field, addedTgt as ValNode)
        } else if (addedTgt is FieldRefNode) { // a.f = b;
            handleStoreEdge(addedTgt.base.p2Set.oldSet, addedTgt.field, addedSrc as ValNode)
        } else if (addedSrc is AllocNode) { // alloc x = new T;
            propagatePTS(addedTgt as VarNode, addedSrc)
        }
    }

    private suspend fun propagateAddedEdges(addedEdges: Queue<Pair<Node, Node>>) {
        /*
         * there are some actual parameter to formal parameter edges whose source nodes are not in the worklist.
         * For this case, we should use the following loop to update the target nodes and insert the
         * target nodes into the worklist if nesseary.
         * */
        val loopEdges = ConcurrentLinkedQueue<Pair<Node, Node>>()
        coroutineScope {
            while (addedEdges.isNotEmpty()) {
                val flow = addedEdges.poll()
                val (addedSrc, addedTgt) = flow
                launch {
                    try {
                        if (noBackEdgeGraph.addEdgeSynchronized(addedSrc, addedTgt)) {
                            synchronized(addedSrc) {
                                synchronized(addedTgt) {
                                    propagateEdge(addedSrc, addedTgt)
                                }
                            }
                        } else {
                            loopEdges += flow
                        }
                    } finally {
                        noBackEdgeGraph.removeEdgeSynchronized(addedSrc, addedTgt)
                    }
                }
            }
        }
        for ((addedSrc, addedTgt) in loopEdges) {
            propagateEdge(addedSrc, addedTgt)
        }
        while (addedEdges.isNotEmpty()) {
            val (addedSrc, addedTgt) = addedEdges.poll()
            propagateEdge(addedSrc, addedTgt)
        }
    }


    private fun propagateSimpleEdge(curr: ValNode, newSet: HybridPointsToSet) {
        for (next in pag.simpleLookup(curr)) {
            if (next == curr)
                continue
            try {
                if (noBackEdgeGraph.addEdgeSynchronized(curr, next)) {
                    synchronized(next) {
                        propagatePTS(next, newSet)
                    }
                } else {
                    // TODO
                }
            } finally {
                noBackEdgeGraph.removeEdgeSynchronized(curr, next)
            }
        }
    }


    protected fun propagatePTS(next: ValNode, newSet: HybridPointsToSet) {
        val sz = newSet.size()
        if (sz == 0) {
            return
        }
        if (sz <= 2) {
            val allocNodeNumberer = pag.allocNodeNumberer
            for (node in newSet.nodeIdxs) {
                if (node == 0) break
                propagatePTS(next, allocNodeNumberer.get(node.toLong()))
            }
            return
        }
        val addTo = next.p2Set
        val toType = next.type
        val p2SetVisitor: P2SetVisitor = object : P2SetVisitor(pta) {
            val castNeverFailsCache = IdentityHashMap<Type, Boolean>(ExpectedSize.capacity(16))
            public override fun visit(node: Node) {
                val nodeType: Type = node.type
                var b = castNeverFailsCache[nodeType]
                if (b == null) {
                    b = PTAUtils.castNeverFails(nodeType, toType)
                    castNeverFailsCache[nodeType] = b
                }
                if (b && addTo.add(node.number)) {
                    returnValue = true
                }
            }
        }
        newSet.forall(p2SetVisitor)
        if (p2SetVisitor.returnValue) {
            valNodeWorkList.add(next)
        }
    }

    protected fun propagatePTS(pointer: ValNode, heap: AllocNode) {
        if (PTAUtils.addWithTypeFiltering(pointer.p2Set, pointer.type, heap)) {
            valNodeWorkList.add(pointer)
        }
    }

    // we do not allow store to and load from constant heap/empty array.
    private fun disallowStoreOrLoadOn(heap: AllocNode): Boolean {
        val base = heap.base()
        // return base instanceof StringConstantNode || PTAUtils.isEmptyArray(base);
        return PTAUtils.isEmptyArray(base)
    }
}
