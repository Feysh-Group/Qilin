package qilin.core.graph

import org.slf4j.LoggerFactory
import soot.toolkits.graph.MutableDirectedGraph
import java.util.*

class HashMutableDirectedGraph<N>(
    private val nodeToPreds: MutableMap<N, MutableSet<N>> = HashMap<N, MutableSet<N>>(),
    private val nodeToSuccs: MutableMap<N, MutableSet<N>> = HashMap<N, MutableSet<N>>(),
    private val heads: MutableSet<N> = HashSet(),
    private val tails: MutableSet<N> = HashSet()
) : MutableDirectedGraph<N>, Cloneable {

    // copy constructor
    constructor(orig: HashMutableDirectedGraph<N>) : this(
        deepCopy<N, N>(orig.nodeToPreds),
        deepCopy<N, N>(orig.nodeToSuccs),
        HashSet(orig.heads),
        HashSet(orig.tails)
    )

    constructor(initialCapacity: Int, headTailsCapacity: Int? = null): this(
        nodeToPreds = HashMap<N, MutableSet<N>>(initialCapacity),
        nodeToSuccs = HashMap<N, MutableSet<N>>(initialCapacity),
        heads = headTailsCapacity?.let { HashSet(headTailsCapacity) } ?: HashSet(),
        tails = headTailsCapacity?.let { HashSet(headTailsCapacity) } ?: HashSet(),
    )

    public override fun clone(): Any {
        return HashMutableDirectedGraph(this)
    }

    /** Removes all nodes and edges.  */
    fun clearAll() {
        nodeToPreds.clear()
        nodeToSuccs.clear()
        heads.clear()
        tails.clear()
    }

    /* Returns an unbacked list of heads for this graph. */
    override fun getHeads(): List<N> {
        return getCopy(heads)
    }

    /* Returns an unbacked list of tails for this graph. */
    override fun getTails(): List<N> {
        return getCopy(tails)
    }

    override fun getPredsOf(s: N): List<N> {
        val preds: Set<N>? = nodeToPreds[s]
        if (preds != null) {
            return getCopy(preds)
        }
        return emptyList()
    }

    /**
     * Same as [.getPredsOf] but returns a set. This is faster than calling [.getPredsOf]. Also,
     * certain operations like [Collection.contains] execute faster on the set than on the list. The returned set
     * is unmodifiable.
     */
    fun getPredsOfAsSet(s: N): Set<N> {
        val preds: Set<N>? = nodeToPreds[s]
        if (preds != null) {
            return Collections.unmodifiableSet(preds)
        }
        return emptySet()
    }

    override fun getSuccsOf(s: N): List<N> {
        val succs: Set<N>? = nodeToSuccs[s]
        if (succs != null) {
            return getCopy(succs)
        }
        return emptyList()
    }

    /**
     * Same as [.getSuccsOf] but returns a set. This is faster than calling [.getSuccsOf]. Also,
     * certain operations like [Collection.contains] execute faster on the set than on the list. The returned set
     * is unmodifiable.
     */
    fun getSuccsOfAsSet(s: N): Set<N> {
        val succs: Set<N>? = nodeToSuccs[s]
        if (succs != null) {
            return Collections.unmodifiableSet(succs)
        }
        return emptySet()
    }

    override fun size(): Int {
        return nodeToPreds.keys.size
    }

    override fun iterator(): MutableIterator<N> {
        return nodeToPreds.keys.iterator()
    }

    override fun addEdge(from: N, to: N) {
        if (containsEdge(from, to)) {
            return
        }
        val succsList = nodeToSuccs.getOrPut(from){
            heads.add(from)
            LinkedHashSet()
        }
        val predsList = nodeToPreds.getOrPut(to){
            tails.add(to)
            LinkedHashSet()
        }
        heads.remove(to)
        tails.remove(from)
        succsList.add(to)
        predsList.add(from)
    }

    override fun removeEdge(from: N, to: N) {
        val succs = nodeToSuccs[from]
        if (succs == null || !succs.contains(to)) {
            // i.e. containsEdge(from, to)==false
            return
        }
        val preds = nodeToPreds[to]
            ?: // i.e. inconsistent data structures
            throw RuntimeException(to.toString() + " not in graph!")
        succs.remove(to)
        preds.remove(from)
        if (succs.isEmpty()) {
            tails.add(from)
            nodeToSuccs.remove(from)
        }
        if (preds.isEmpty()) {
            heads.add(to)
            nodeToPreds.remove(to)
        }
        removeSingle(from)
        removeSingle(to)
    }

    private fun removeSingle(n: N){
        val succs = nodeToSuccs[n]
        val preds = nodeToPreds[n]
        if (succs?.isNotEmpty() != true && heads.contains(n)){
            heads.remove(n)
        }
        if (preds?.isNotEmpty() != true && tails.contains(n)){
            tails.remove(n)
        }
    }

    override fun containsEdge(from: N, to: N): Boolean {
        val succs: Set<N>? = nodeToSuccs[from]
        return succs != null && succs.contains(to)
    }

    override fun containsNode(node: N): Boolean {
        return nodeToPreds.keys.contains(node)
    }

    override fun getNodes(): List<N> {
        return getCopy(nodeToPreds.keys)
    }

    override fun addNode(node: N) {
        if (containsNode(node)) {
            return
        }
        nodeToSuccs.getOrPut(node) { LinkedHashSet() }
        nodeToPreds.getOrPut(node) { LinkedHashSet() }
        heads.add(node)
        tails.add(node)
    }

    override fun removeNode(node: N) {
        for (n in ArrayList(nodeToSuccs[node])) {
            removeEdge(node, n)
        }
        nodeToSuccs.remove(node)
        for (n in ArrayList(nodeToPreds[node])) {
            removeEdge(n, node)
        }
        nodeToPreds.remove(node)
        heads.remove(node)
        tails.remove(node)
    }

    fun printGraph() {
        for (node in this) {
            logger.debug("Node = $node")
            logger.debug("Preds:")
            for (p in getPredsOf(node)) {
                logger.debug("     ")
                logger.debug("" + p)
            }
            logger.debug("Succs:")
            for (s in getSuccsOf(node)) {
                logger.debug("     ")
                logger.debug("" + s)
            }
        }
    }

    companion object {
        private val logger = LoggerFactory.getLogger(HashMutableDirectedGraph::class.java)
        private fun <T> getCopy(c: Collection<T>): List<T> {
            return Collections.unmodifiableList(ArrayList(c))
        }

        private fun <A, B> deepCopy(`in`: Map<A, MutableSet<B>>): MutableMap<A, MutableSet<B>> {
            val retVal = HashMap(`in`)
            for (e in retVal.entries) {
                e.setValue(LinkedHashSet(e.value))
            }
            return retVal
        }
    }
}