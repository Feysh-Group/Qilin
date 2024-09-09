package qilin.core.graph

import java.util.*

// 一个多线程的顺序依赖有向图图, 可以检测添加的 edge 是否为一个环
class NoBackEdgeDirectGraph<N>(
    private var predView: MutableMap<N, MutableMap<N, MutableSet<N>>> = hashMapOf(),
    private var directedGraph: HashMutableDirectedGraph<N> = HashMutableDirectedGraph()
) {


    fun getPredsTaskOf(from: N): MutableSet<N> {
        val predTaskOfFrom = mutableSetOf<N>()
        for (pred in directedGraph.getPredsOfAsSet(from)) {
            // get values of pred to from
            val predOfFrom = predView[pred]?.get(from) ?: continue
            predTaskOfFrom.addAll(predOfFrom)
        }
        return predTaskOfFrom
    }

    // pred ->
    //         -> from -> to -> succ
    // pred ->
    @Suppress("MemberVisibilityCanBePrivate")
    fun addEdge(from: N, to: N): Boolean {
        // detect loop
        if (from == to) {
            return false
        }

        val predTaskOfFrom = getPredsTaskOf(from)
        if (predTaskOfFrom.contains(to)) {
            return false
        }

        predTaskOfFrom.add(from)
        directedGraph.addEdge(from, to)

        // update successors
        val workList: Queue<N> = LinkedList()
        workList.add(from)
        val set = hashSetOf<N>()
        set.add(from)
        while (!workList.isEmpty()) {
            val cur = workList.poll()
            val succ = directedGraph.getSuccsOfAsSet(cur)
            for (next in succ) {
                var curView = predView[cur]
                if (curView == null) {
                    curView = hashMapOf()
                    predView[cur] = curView
                }
                var predTaskOfCur = curView[next]
                if (predTaskOfCur == null) {
                    predTaskOfCur = hashSetOf()
                    curView[next] = predTaskOfCur
                }
                if (!predTaskOfCur.containsAll(predTaskOfFrom)) {
                    if (set.add(next)) {
                        workList.add(next)
                    }
                    predTaskOfCur.addAll(predTaskOfFrom)
                }
            }
        }
        return true
    }

    // pred ->
    //         -> from -> to -> succ
    // pred ->
    fun removeEdge(from: N, to: N) {
        directedGraph.removeEdge(from, to)
        val predOfFrom = predView[from]?.also { it.remove(to) }
        if (predOfFrom?.isEmpty() == true) {
            predView.remove(from)
        }
    }

    fun getPredSize(from: N): Int {
        synchronized(this) {
            val predTaskOfFrom = getPredsTaskOf(from)
            return predTaskOfFrom.size
        }
    }

    fun addEdgeSynchronized(from: N, to: N): Boolean {
        synchronized(this) {
            return addEdge(from, to)
        }
    }


    fun removeEdgeSynchronized(from: N, to: N) {
        synchronized(this) {
            removeEdge(from, to)
        }
    }

    val isComplete: Boolean
        get() = predView.isEmpty() && directedGraph.size() == 0 && directedGraph.heads.isEmpty() && directedGraph.tails.isEmpty()

}
