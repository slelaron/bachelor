import java.io.File
import java.io.InputStream
import java.lang.Exception
import java.util.*
import kotlin.math.roundToInt

sealed class Recording
data class Marker(val id: Int = Random().nextInt(), var valid: Boolean = true): Recording()
data class Action(val undo: () -> Unit): Recording()

val recordings = mutableListOf<Recording>()

fun<K, V> MutableMap<K, V>.addAndRecord(key: K, value: V) {
    val old = this[key]
    recordings += when (old) {
        null -> Action { this -= key }
        else -> Action { this[key] = old }
    }
    this[key] = value
}

fun<K, V> MutableMap<K, V>.removeAndRecord(key: K) {
    val old = this[key]
    if (old != null) {
        recordings += Action { this[key] = old }
    }
    this -= key
}

fun<T> MutableList<T>.addAndRecord(value: T) {
    recordings += Action { removeAt(size - 1) }
    add(value)
}

fun<T> MutableSet<T>.addAndRecord(value: T) {
    if (value !in this) {
        recordings += Action { this -= value }
    }
    this += value
}

fun<T> MutableList<T>.addAllAndRecord(coll: Collection<T>) {
    val sz = size
    recordings += Action {
        while (size != sz) {
            removeAt(size - 1)
        }
    }
    addAll(coll)
}

fun<T> MutableSet<T>.addAllAndRecord(coll: Collection<T>) {
    val notHere = coll - this
    recordings += Action { this -= notHere }
    addAll(coll)
}

fun Color.setAndRecord(value: Boolean) {
    val old = red
    recordings += Action { red = old }
    red = value
}

fun RTA.setNumberAndRecord(value: Long) {
    val old = number
    recordings += Action { number = old }
    number = value
}

fun getMarker() = Marker().also { recordings += it }

fun undo(marker: Marker) {
    if (!marker.valid) throw Exception("Non-valid marker")
    while (true) {
        when (val res = recordings.lastOrNull()) {
            null -> throw Exception("There is no recordings in recordings")
            is Marker -> {
                res.valid = false
                if (res == marker) return
            }
            is Action -> {
                res.undo()
            }
        }
        recordings.removeAt(recordings.size - 1)
    }
}

fun clearRecordings() {
    recordings.clear()
}

data class Color(var red: Boolean = false)

class RTA(override val ways: MutableMap<Conditions, Pair<Set<Timer>, RTA>> = mutableMapOf(),
          var number: Long,
          private val red: Color = Color()): Automaton(ways, null, "q$number") {
    val tails = mutableMapOf<Conditions, MutableList<Trace>>()
    private val ends = mutableSetOf<Trace>()

    val isRed
        get() = red.red

    override val name
        get() = "q$number"

    override val final: Boolean?
        get() {
            return when (ends.any { it.acceptable } to ends.any { !it.acceptable }) {
                true to false -> true
                false to true -> false
                else -> null
            }
        }

    override operator fun get(label: String, timerManager: TimerManager) = ways.nextState(label, timerManager)
    operator fun get(label: String, time: Int) = get(label, TimerManager().apply { global += time }).map { it.second }
    operator fun set(label: String, range: IntRange, target: RTA) {
        ways.addAndRecord(Conditions(label, mapOf(1 to range)), oneTimerSet to target)
    }

    fun addTraces(traces: Iterable<Trace>, inf: Int = Int.MAX_VALUE) {
        val (go, here) = traces.partition { it.records.firstOrNull() != null }
        ends.addAll(here)

        for ((label, list) in go.groupBy { it.records.first().name }) {
            var cnt = 0
            val key = Conditions(label, mapOf(1 to 0..inf))
            val target = ways.getOrPut(key) { cnt++; oneTimerSet to RTA(number = next++) }.second
            val t = tails.getOrPut(key) { cnt++; mutableListOf() }
            if (cnt == 1) throw Exception("Inconsistent rta")
            t.addAll(list)
            target.addTraces(list.map { it.copy(records = it.records.subList(1, it.records.size)) }, inf = inf)
        }
    }

    fun split(label: String, range: IntRange, at: Int, inf: Int = Int.MAX_VALUE) {
        if (at !in range || at == range.endInclusive) throw Exception("$at !in $range")
        val target = ways[Conditions(label, mapOf(1 to range))]
        val traces = tails[Conditions(label, mapOf(1 to range))]
        if (target == null && traces == null) return
        if (target == null || traces == null) throw Exception("Inconsistent automaton")
        ways.removeAndRecord(Conditions(label, mapOf(1 to range)))
        tails.removeAndRecord(Conditions(label, mapOf(1 to range)))
        val (down, up) = traces.partition { it.records.first().time <= at }
        val downTree = buildTAPTA(down.map { it.copy(records = it.records.subList(1, it.records.size))}, inf = inf)
        val upTree = buildTAPTA(up.map { it.copy(records = it.records.subList(1, it.records.size))}, inf = inf)
        ways.addAndRecord(Conditions(label, mapOf(1 to range.first..at)), oneTimerSet to downTree)
        tails.addAndRecord(Conditions(label, mapOf(1 to range.first..at)), down.toMutableList())
        ways.addAndRecord(Conditions(label, mapOf(1 to (at + 1)..range.endInclusive)), oneTimerSet to upTree)
        tails.addAndRecord(Conditions(label, mapOf(1 to (at + 1)..range.endInclusive)), up.toMutableList())
        setNumberAndRecord(next++)
    }

    fun isConsistent(): Boolean {
        val visited = mutableSetOf<Long>()
        fun RTA.consistent(): Boolean {
            visited += number
            if (ends.isNotEmpty() && final == null) return false
            if (ways.keys != tails.keys) throw Exception("Inconsistency")
            for (way in ways.keys) {
                val target = ways[way]?.second ?: throw Exception("Something strange")
                val tails = tails[way] ?: throw Exception("Full inconsistency")
                if (target.number !in visited) {
                    when (target.isRed) {
                        true -> {
                            val res = target.consistent()
                            if (!res) return false
                        }
                        false -> {
                            val (pos, neg) = tails.partition { it.acceptable }
                            if (pos.map { it.records }.intersect(neg.map { it.records }).isNotEmpty()) {
                                //System.err.println("Intersection problem")
                                return false
                            }
                        }
                    }
                }
            }
            return true
        }
        return consistent()
    }

    fun merge(that: RTA, theEdge: AutomatonEdge<RTA>, inf: Int = Int.MAX_VALUE, needEdgeCorrection: Boolean): Boolean {
        if (!isRed) throw Exception("not red state")
        val was = mutableSetOf<Long>()
        val visited = mutableListOf<RTA>()
        was += theEdge.from.number
        visited += theEdge.from
        if (theEdge.to.number !in was) {
            was += theEdge.to.number
            visited += theEdge.to
        }
        fun RTA.doMerge(edge: AutomatonEdge<RTA>): Boolean {
            val rhs = edge.to
            //System.err.println("doMerge: ${this.name} ${rhs.name}")
            if (isRed && rhs.ends.isNotEmpty() && ends.isNotEmpty() && final != rhs.final) {
                //System.err.println("NO: q$number q${rhs.number}")
                return false
            }
            if (number !in was) {
                was += number
                visited += this
            }
            if (rhs.isRed) throw Exception("red state, strange")
            ends.addAllAndRecord(rhs.ends)
            val label2guard = ways.keys.
                groupBy({ it.label }) { it.timeGuards[1] ?: throw Exception("No 1 timer!!") }.
                mapValues { (_, value) -> value.map { it.last }.sorted() }.
                mapValues { (_, value) ->
                    if (value.last() != inf) throw Exception("last = ${value.last()}")
                    value.dropLast(1)
                }
            for ((label, guards) in rhs.ways.keys.toList()) {
                val range = guards[1] ?: throw Exception("No 1 timer")
                if (range.start != 0 || range.last != inf) throw Exception("Not valid constraints")
                val splitters = label2guard[label]
                var prev = 0
                if (splitters != null) {
                    for (point in splitters) {
                        rhs.split(label, prev..inf, point, inf = inf)
                        prev = point + 1
                    }
                }
            }
            edge.from.ways.addAndRecord(edge.conditions, oneTimerSet to this)
            val toMerge = mutableListOf<Pair<RTA, AutomatonEdge<RTA>>>()
            for ((cond, value) in rhs.ways) {
                val t = rhs.tails[cond] ?: throw Exception("Inconsistent rhs")
                val target = ways[cond]?.second
                val tt = tails[cond]
                if ((target == null) xor (tt == null)) throw Exception("Inconsistency")
                if (target == null || tt == null) {
                    ways.addAndRecord(cond, oneTimerSet to value.second)
                    tails.addAndRecord(cond, t)
                } else {
                    toMerge += target to AutomatonEdge(rhs, value.second, cond, oneTimerSet)
                    tt.addAllAndRecord(t)
                }
            }
            for ((a, b) in toMerge) {
                val res = a.doMerge(b)
                if (!res) return false
            }
            return true
        }
        val res = that.doMerge(theEdge)
        if (!res || !needEdgeCorrection) return res
        //System.err.println("Visited: ${visited.joinToString(" ") { it.name }}")
        for (state in visited) {
            state.setNumberAndRecord(next++)
        }
        for (state in visited) {
            val label2Edge = mutableMapOf<String, MutableList<Pair<IntRange, Pair<RTA, List<Trace>>>>>()
            for (cond in state.ways.keys) {
                val target = state.ways[cond]?.second ?: throw Exception("Strange")
                val t = state.tails[cond] ?: throw Exception("Inconsistency")
                val list = label2Edge.getOrPut(cond.label) { mutableListOf() }
                val range = cond.timeGuards[1] ?: throw Exception("No 1 timer")
                list += range to (target to t)
            }
            for ((label, list) in label2Edge) {
                list.sortBy { it.first.first }
                var start = 0
                var end = 0
                for (i in 1..list.size) {
                    if (i == list.size || list[i].second.first.name != list[start].second.first.name) {
                        if (start != end) {
                            for (j in start..end) {
                                val key = Conditions(label, mapOf(1 to list[j].first))
                                state.ways.removeAndRecord(key)
                                state.tails.removeAndRecord(key)
                            }
                            val cond = Conditions(
                                label,
                                mapOf(1 to list[start].first.first..list[end].first.endInclusive)
                            )
                            state.ways.addAndRecord(
                                cond,
                                oneTimerSet to list[start].second.first
                            )
                            state.tails.addAndRecord(
                                cond,
                                (start..end).flatMap { list[it].second.second }.toMutableList()
                            )
                        }
                        start = i
                        end = i
                    } else {
                        end++
                    }
                }
            }
        }
        return true
    }

    private fun changeBad(was: RTA, need: RTA) {
        val visited = mutableSetOf<Long>()
        fun RTA.doChange() {
            visited += number
            for ((_, next) in ways.values) {
                if (next.number !in visited) {
                    next.doChange()
                }
            }
            val toChange = mutableListOf<Pair<Conditions, Pair<Set<Timer>, RTA>>>()
            for ((conditions, value) in ways) {
                if (value.second == was) toChange += conditions to (value.first to need)
            }
            for ((key, value) in toChange) {
                ways.addAndRecord(key, value)
            }
        }
        doChange()
    }

    fun color(): Boolean {
        if (ends.isNotEmpty() && final == null) return false
        if (ways.keys != tails.keys) throw Exception("Inconsistency")
        for (way in ways.keys) {
            val tails = tails[way] ?: throw Exception("Full inconsistency")
            val (pos, neg) = tails.partition { it.acceptable }
            if (pos.map { it.records }.intersect(neg.map { it.records }).isNotEmpty()) {
                return false
            }
        }
        red.setAndRecord(true)
        return true
    }

    fun consistentMeasure(): Int {
        val visited = mutableSetOf<Long>()
        fun RTA.doConsistent(): Int {
            visited += number
            var sum = 0
            for (next in ways.values.map { it.second }) {
                if (next.number !in visited) {
                    sum += next.doConsistent()
                }
            }
            val (good, bad) = ends.partition { it.acceptable }
            val a = good.size
            val b = bad.size
            return sum + a * (a - 1) / 2 + b * (b - 1) / 2 - a * b
        }
        return doConsistent()
    }

    companion object {
        val oneTimerSet = setOf(1)
        var next = 0L
    }
}

fun parseConsoleArgumentsVerwerAutomaton(args: Array<String>): InputStream {
    val map = parseConsoleArguments(args)
    return map.getFirstArg(listOf("-s", "--source"), System.`in`) { File(it[0]).inputStream() }
}

fun getVerwerRTA(input: InputStream): Automaton {
    val theScanner = Scanner(input)
    theScanner.nextLine()
    val n = theScanner.nextInt()
    val alphabetSize = theScanner.nextInt()
    val list = (-1 until n).map { it to MutableAutomaton(name = "q${it + 1}") }.toMap()
    val alphabet = List(alphabetSize) { ('a' + it).toString() }
    theScanner.nextLine()
    for (i in 0 until n) {
        val str = theScanner.nextLine()
        System.err.println(str)
        val scanner = Scanner(str)
        val now = scanner.nextInt()
        val final = scanner.nextInt()
        list[now]!!.final = final == 1
        while (scanner.hasNext()) {
            val sym = scanner.nextInt()
            scanner.next()
            var next = scanner.next()
            var start = 0
            while (true) {
                val after = next.toDouble().roundToInt()
                val go = scanner.nextInt()
                System.err.println("$now[$start..$after] -> $go")
                list[now]!!.ways[Conditions(
                    label = alphabet[sym],
                    timeGuards = mapOf(1 to start..after)
                )] = setOf(1) to list[go]!!
                start = after + 1
                next = scanner.next()
                if (next == "]") break
                next = scanner.next()
            }
        }
    }
    return list[0]!!
}

fun main(args: Array<String>) {
    val input = parseConsoleArgumentsVerwerAutomaton(args)
    val automaton = getVerwerRTA(input)
    println(automaton)
    //automaton.createDotFile(name = "verwer_result", inf = 10000)
}
