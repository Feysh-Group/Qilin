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

package qilin.stat;

import com.google.common.collect.Sets;
import com.google.common.util.concurrent.AtomicDouble;
import qilin.CoreConfig;
import qilin.core.PTA;
import qilin.core.PTAScene;
import qilin.core.builder.FakeMainFactory;
import qilin.core.builder.MethodNodeFactory;
import qilin.core.pag.*;
import qilin.core.sets.ExpectedSize;
import qilin.core.sets.PointsToSet;
import qilin.util.PTAUtils;
import qilin.util.Stopwatch;
import soot.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.util.ArraySet;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

public class SimplifiedEvaluator implements IEvaluator {
    protected final PTA pta;
    protected final Exporter exporter;
    protected Stopwatch stopwatch;

    public SimplifiedEvaluator(PTA pta) {
        this.pta = pta;
        exporter = new Exporter();
    }

    @Override
    public void begin() {
        stopwatch = Stopwatch.newAndStart("PTA evaluator");
    }

    @Override
    public void end() {
        stopwatch.stop();
        exporter.collectMetric("Time (sec):", String.valueOf(((double) stopwatch.elapsed())));
        exporter.collectMetric("#Reachable Method (CI):", String.valueOf(pta.getNakedReachableMethods().size() - 1));
        CallGraph ciCallGraph = pta.getCallGraph();
        exporter.collectMetric("#Call Edge(CI):", String.valueOf(ciCallGraph.size() - FakeMainFactory.implicitCallEdges));

        CallGraph callGraph = pta.getCallGraph();

        // loop over all reachable method's statement to find casts, local
        // references, virtual call sites
        Set<SootMethod> reachableMethods = new HashSet<>();
        for (MethodOrMethodContext momc : pta.getCgb().getReachableMethods()) {
            final SootMethod sm = momc.method();
            reachableMethods.add(sm);
        }
        int totalPolyCalls = 0;
        int totalCastsMayFail = 0;
        for (SootMethod sm : reachableMethods) {
            // All the statements in the method
            for (Unit unit : PTAUtils.getMethodBody(sm).getUnits()) {
                Stmt st = (Stmt) unit;
                // virtual calls
                if (st.containsInvokeExpr()) {
                    InvokeExpr ie = st.getInvokeExpr();
                    if (!(ie instanceof StaticInvokeExpr)) {
                        // Virtual, Special or Instance
                        // have to check target soot method, cannot just
                        // count edges
                        Set<SootMethod> targets = new HashSet<>();
                        for (Iterator<Edge> it = callGraph.edgesOutOf(st); it.hasNext(); )
                            targets.add(it.next().tgt());
                        if (targets.size() > 1) {
                            totalPolyCalls++;
                        }
                    }
                } else if (st instanceof AssignStmt) {
                    Value rhs = ((AssignStmt) st).getRightOp();
                    Value lhs = ((AssignStmt) st).getLeftOp();
                    if (rhs instanceof CastExpr && lhs.getType() instanceof RefLikeType) {
                        final Type targetType = ((CastExpr) rhs).getCastType();
                        Value v = ((CastExpr) rhs).getOp();
                        if (!(v instanceof Local)) {
                            continue;
                        }
                        boolean fails = false;
                        Collection<AllocNode> pts = pta.reachingObjects((Local) v).toCollection();
                        for (Node n : pts) {
                            if (fails) {
                                break;
                            }
                            fails = !PTAUtils.castNeverFails(n.getType(), targetType);
                        }
                        if (fails) {
                            totalCastsMayFail++;
                        }
                    }
                }
            }
        }
        exporter.collectMetric("#May Fail Cast (Total):", String.valueOf(totalCastsMayFail));
        exporter.collectMetric("#Virtual Call Site(Polymorphic):", String.valueOf(totalPolyCalls));
        if (CoreConfig.v().getPtaConfig().printAliasInfo) {
            AliasStat aliasStat = new AliasStat(pta);
            aliasStat.aliasesProcessing();
            exporter.collectMetric("#globalAlias_incstst:", String.valueOf(aliasStat.getGlobalAliasesIncludingStSt()));
            ptsStat();
        }
    }

    private void ptsStat() {
        AtomicDouble ptsCntNoNative = new AtomicDouble(0);
        AtomicInteger varCntNoNative = new AtomicInteger(0);
        PAG pag = pta.getPag();
        // locals exclude Exceptions
        for (Local local : pag.getLocalPointers()) {
            try {
                LocalVarNode lvn = pag.findLocalVarNode(local);
                if (local.toString().contains("intermediate/")) {
                    continue;
                }
                mLocalVarNodes.add(lvn);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }

        // stat avg pts.
        for (SootMethod sm : pta.getNakedReachableMethods()) {
            MethodPAG mpag = pag.getMethodPAG(sm);
            MethodNodeFactory mnf = mpag.nodeFactory();
            if (!sm.isStatic()) {
                mLocalVarNodes.add((LocalVarNode) mnf.caseThis());
            }
            for (int i = 0; i < sm.getParameterCount(); ++i) {
                Type mType = sm.getParameterType(i);
                if (mType instanceof RefLikeType) {
                    mLocalVarNodes.add((LocalVarNode) mnf.caseParm(i));
                }
            }
        }
        Set<LocalVarNode> tmp = Collections.newSetFromMap(new ConcurrentHashMap<>(ExpectedSize.capacity(mLocalVarNodes.size() / 10)));
        mLocalVarNodes.parallelStream().forEach( (lvn) -> {
                SootMethod sm = lvn.getMethod();
                if (PTAUtils.isFakeMainMethod(sm)) {
                    tmp.add(lvn);
                    return;
                }
                final Set<Object> callocSites = getPointsToNewExpr(pta.reachingObjects(lvn));
                if (!callocSites.isEmpty()) {
                    if (!handledNatives.contains(sm.toString())) {
                        ptsCntNoNative.addAndGet(callocSites.size());
                        varCntNoNative.incrementAndGet();
                    }
                } else {
                    tmp.add(lvn);
                }
            }
        );
        mLocalVarNodes.removeAll(tmp);

        exporter.collectMetric("#Avg Points-to Target without Native Var(CI):", String.valueOf((ptsCntNoNative.get()) / (varCntNoNative.get())));
    }

    private final Set<String> handledNatives = Set.of(
            "<org.apache.xerces.parsers.XML11Configuration: boolean getFeature0(java.lang.String)>",
            "<java.lang.ref.Finalizer: void invokeFinalizeMethod(java.lang.Object)>",
            "<java.lang.Thread: java.lang.Thread currentThread()>",
            "<java.lang.Thread: void start0()>",
            "<java.lang.Object: java.lang.Object clone()>",
            "<java.lang.System: void setIn0(java.io.InputStream)>",
            "<java.lang.System: void setOut0(java.io.PrintStream)>",
            "<java.lang.System: void setErr0(java.io.PrintStream)>",
            "<java.io.FileSystem: java.io.FileSystem getFileSystem()>",
            "<java.io.UnixFileSystem: java.lang.String[] list(java.io.File)>",
            "<java.security.AccessController: java.lang.Object doPrivileged(java.security.PrivilegedAction)>",
            "<java.security.AccessController: java.lang.Object doPrivileged(java.security.PrivilegedAction,java.security.AccessControlContext)>",
            "<java.security.AccessController: java.lang.Object doPrivileged(java.security.PrivilegedExceptionAction)>",
            "<java.security.AccessController: java.lang.Object doPrivileged(java.security.PrivilegedExceptionAction,java.security.AccessControlContext)>"
    );

    private final Set<LocalVarNode> mLocalVarNodes = new HashSet<>();

    protected Set<Object> getPointsToNewExpr(PointsToSet pts) {
        return pts.toCollection(Sets.newHashSetWithExpectedSize(pts.size()), AllocNode::getNewExpr);
    }

    @Override
    public String toString() {
        return exporter.report();
    }
}
