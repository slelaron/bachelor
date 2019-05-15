import java.io.File
import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Paths
import java.util.*

data class Record(val name: String, val time: Int)

class Tree(val ways: Map<Record, Tree>, val acceptable: Boolean?)

class MutableTree(private val ways: MutableMap<Record, MutableTree> = mutableMapOf(), var acceptable: Boolean? = null) {
    fun toTree(): Tree = Tree(ways.mapValues { it.value.toTree() }, acceptable)

    fun addTrace(trace: Trace) {
        val next = ways.getOrPut(trace.records.firstOrNull() ?: let {
            if (acceptable != null && acceptable != trace.acceptable) {
                throw IllegalStateException("Inconsistent traces")
            }
            acceptable = trace.acceptable
            return
        }) { MutableTree() }
        next.addTrace(Trace(trace.records.subList(1, trace.records.size), trace.acceptable))
    }
}

typealias Timer = Int

data class Conditions(val label: String, val timeGuards: Map<Timer, IntRange>) {
    fun suit(label: String, timerManager: TimerManager) =
        label == this.label && timeGuards.all { timerManager[it.key] in it.value }
}

sealed class Either<T, E>
data class ErrorContainer<T, E>(val error: E): Either<T, E>()
data class AnswerContainer<T, E>(val answer: T): Either<T, E>()

class MutableAutomaton(
    val ways: MutableMap<Conditions, Pair<Set<Timer>, MutableAutomaton>> = mutableMapOf(),
    var final: Boolean = false,
    val name: String) {

    fun nextState(label: String,
                  timerManager: TimerManager): Either<Pair<Set<Timer>, MutableAutomaton>, String> {
        val possibleWays = ways.filterKeys { it.suit(label, timerManager) }.values.toList()
        if (possibleWays.size > 1) {
            return ErrorContainer("There is more than one way to go: need={$label, $timerManager}, have=$ways")
        }
        val possibleAutomaton = possibleWays.firstOrNull()
            ?: return ErrorContainer("There is no way to go: need={$label, $timerManager}, have=${ways.filterKeys { it.label == label }}")
        return AnswerContainer(possibleAutomaton)
    }
}

data class Trace(val records: List<Record>, val acceptable: Boolean)

data class Edge<T>(val from: Int, val to: Int, val data: T)

fun normalize(rawTrace: Trace) =
        Trace(rawTrace.records.zipWithNext { a, b ->
            Record(b.name, b.time - a.time)
        }, rawTrace.acceptable) // plug until there are bad traces, after some time it doesn't need any more

fun buildPrefixTree(traces: List<Trace>): Tree {
    val tree = MutableTree()
    for (trace in traces) {
        tree.addTrace(trace)
    }
    return tree.toTree()
}

data class AnnotatedTrace(val trace: Trace, val reason: String)

data class Verdict(val correct: List<Trace>, val incorrect: List<AnnotatedTrace>)

class TimerManager {
    private val timer2Time = mutableMapOf<Timer, Int>()
    var global = 0
        set(new: Int) {
            field = new.takeIf { it >= global } ?: throw IllegalStateException("New time must be more than previous")
        }

    operator fun get(timer: Timer) = global - timer2Time.getOrPut(timer) { 0 }

    fun reset(timer: Timer) {
        timer2Time[timer] = global
    }

    override fun toString() = "Manager(globalTime=$global, timer2time=$timer2Time)"
}

fun MutableAutomaton.checkAllTraces(traces: List<Trace>): Verdict {
    val result = traces.map {
        val timerManager = TimerManager()
        var state = this
        for (record in it.records) {
            timerManager.global += record.time
            val possibleNext = state.nextState(record.name, timerManager)
            state = when (possibleNext) {
                is ErrorContainer -> {
                    return@map AnnotatedTrace(it, possibleNext.error)
                }
                is AnswerContainer -> {
                    for (timer in possibleNext.answer.first) {
                        timerManager.reset(timer)
                    }
                    possibleNext.answer.second
                }
            }
        }
        AnnotatedTrace(it, if (state.final) "" else "Nonterminal state")
    }
    return Verdict(result.filter { it.reason == "" }.map { it.trace }, result.filter { it.reason != "" })
}

fun MutableAutomaton.checkAllTraces(traces: ProgramTraces): Pair<Verdict, Verdict> =
        Pair(checkAllTraces(traces.validTraces), checkAllTraces(traces.invalidTraces))

fun parseMinizincOutput(scanner: Scanner, statesNumber: Int): MutableAutomaton {
    val finalCount = scanner.nextInt()
    val finals = List(finalCount) { scanner.nextInt() }.toSet()
    val automatonStates = List(statesNumber) {
        MutableAutomaton(name = "${it + 1}", final = finals.contains(it + 1))
    }
    val edgeCount = scanner.nextInt()
    for (edge in 0 until edgeCount) {
        val from = scanner.nextInt()
        val to   = scanner.nextInt()
        val label = scanner.next()

        val timerNumber = scanner.nextInt()
        val conditions = Conditions(label, List(timerNumber) {
            val timer = scanner.nextInt()
            val leftBorder = scanner.nextInt()
            val rightBorder = scanner.nextInt()
            timer to leftBorder..rightBorder
        }.toMap())
        val resetNumber = scanner.nextInt()
        automatonStates[from - 1].ways[conditions] = Pair(
            List(resetNumber) { scanner.nextInt() }.toSet(),
            automatonStates[to - 1])
    }
    return automatonStates[0]
}

data class AutomatonEdge(val from: String, val to: String, val conditions: Conditions, val resets: Set<Timer>)

fun MutableAutomaton.createDotFile(name: String) {
    val states = mutableListOf<Pair<String, Boolean>>()
    val edges = mutableListOf<AutomatonEdge>()
    fun visitAutomaton(visited: MutableSet<String>, state: MutableAutomaton) {
        visited += state.name
        states += Pair(state.name, state.final)
        for ((key, value) in state.ways) {
            val nextState = value.second
            edges += AutomatonEdge(state.name, nextState.name, key, value.first)
            if (nextState.name !in visited) {
                visitAutomaton(visited, nextState)
            }
        }
    }
    visitAutomaton(mutableSetOf(), this)
    PrintWriter("$name.dot").apply {
        println("digraph L {")
        for (state in states) {
            with(state) {
                println("\tq$first[label=$first${
                    when (second) {
                        true -> " shape=doublecircle"
                        else -> ""
                    }
                }]")
            }
        }
        for (edge in edges) {
            with(edge) {
                println("\tq$from -> q$to[label=\"${conditions.label}\\n${
                    resets.joinToString("") { "r(t$it)\\n" }
                }${
                    conditions.timeGuards.entries.
                        joinToString("\\n") { "${it.value.first} <= t${it.key} <= ${it.value.last}" }
                }\"]")
            }
        }
        println("}")
        flush()
    }.close()

    val dot = ProcessBuilder("dot", "-Tps", "$name.dot", "-o", "$name.ps").start()
    dot.waitFor()
    System.err.println(dot.errorStream.readAllBytes().toString(Charsets.UTF_8))
    dot.destroy()
}

fun Tree.createDotFile(name: String) {
    val (edges, vertexes) = this.edgesAndVertexes
    PrintWriter("$name.dot").apply {
        println("digraph L {")
        for ((i, acc) in vertexes.withIndex()) {
	    println("\tq${i + 1}[label=${i + 1}${
                when (acc) {
                    null -> ""
                    true -> " shape=doublecircle"
                    else -> " shape=octagon"
                }
            }]")
        }
        for (edge in edges) {
            with(edge) {
                println("\tq$from->q$to[label=\"${data.name}, ${data.time}\"]")
            }
        }
        println("}")
        flush()
    }.close()

    val dot = ProcessBuilder("dot", "-Tps", "$name.dot", "-o", "$name.ps").start()
    dot.waitFor()
    System.err.println(dot.errorStream.readAllBytes().toString(Charsets.UTF_8))
    dot.destroy()
}

val Tree.edgesAndVertexes: Pair<List<Edge<Record>>, List<Boolean?>>
    get() {
        val vertexes = mutableListOf<Boolean?>()
        val edges = mutableListOf<Edge<Record>>()
        fun Tree.get() {
            val number = vertexes.size + 1
            vertexes += acceptable
            for ((record, internal) in ways) {
                edges += Edge(number, vertexes.size + 1, record)
                internal.get()
            }
        }
        get()
        return edges to vertexes
    }

fun writeDataIntoDzn(tree: Tree,
                     statesNumber: Int,
                     vertexDegree: Int,
                     additionalTimersNumber: Int,
                     maxActiveTimersCount: Int,
                     maxTotalEdges: Int,
                     inf: Int) {
    val (edges, vertexes) = tree.edgesAndVertexes
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("prefix_data.dzn").apply {
        println("V = $statesNumber;")
        println("E = $vertexDegree;")
        println("M = ${edges.size};")
        println("T = $additionalTimersNumber;")
        println("TC = $maxActiveTimersCount;")
        println("S = { ${symbols.joinToString()} };")
        println("labels = ${edges.map { it.data.name }};")
        println("prev = ${edges.map { it.from }};")
        println("next = ${edges.map { it.to }};")
        println("times = ${edges.map { it.data.time }};")
        println("acc = ${vertexes.map {
            when(it) {
                true -> "B"
                false -> "W"
                else -> "G"
            }
        }};")
        println("TE = $maxTotalEdges;")
        println("inf = $inf;")
    }.close()
}

fun writeDataIntoTmpDzn(scanner: Scanner,
                        tree: Tree,
                        statesNumber: Int,
                        vertexDegree: Int,
                        additionalTimersNumber: Int) {
    val (edges, _) = tree.edgesAndVertexes
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("tmp.dzn").apply {
        println("V = $statesNumber;")
        println("E = $vertexDegree;")
        println("T = $additionalTimersNumber;")
        println("S = { ${symbols.joinToString()} };")
        while (true) {
            if (!scanner.hasNextLine() ||
                scanner.hasNext("----------") ||
                scanner.hasNext("==========")) {
                break
            }
            println(scanner.nextLine())
        }
    }.close()
}

fun executeMinizinc(): Scanner? {
    val minizinc = ProcessBuilder(
        "minizinc",
        "automaton_cbs.mzn",
        "prefix_data.dzn",
        "--solver", "org.chuffed.chuffed",
        "-o", "tmp").start()
    minizinc.waitFor()
    val output = minizinc.inputStream.readAllBytes().toString(Charsets.UTF_8)
    System.err.println(minizinc.errorStream.readAllBytes().toString(Charsets.UTF_8))
    val scanner = Scanner(Paths.get("tmp").toFile())
    return when (scanner.hasNext("=====UNSATISFIABLE=====") ||
            output.startsWith("=====UNSATISFIABLE=====")) {
        false -> scanner
        else -> {
            scanner.close()
            null
        }
    }.also { minizinc.destroy() }
}

fun getAutomaton(prefixTree: Tree,
                 statesNumber: Int,
                 vertexDegree: Int,
                 additionalTimersNumber: Int,
                 scanner: Scanner): MutableAutomaton {
    writeDataIntoTmpDzn(
        scanner,
        prefixTree,
        statesNumber,
        vertexDegree,
        additionalTimersNumber)
    scanner.close()

    val automatonPrinter = ProcessBuilder(
        "minizinc",
        "automaton_printer.mzn",
        "tmp.dzn",
        "-o", "tmp1").start()
    automatonPrinter.waitFor()
    System.err.println(automatonPrinter.errorStream.readAllBytes().toString(Charsets.UTF_8))
    automatonPrinter.destroy()

    return parseMinizincOutput(Scanner(Paths.get("tmp1").toFile()), statesNumber)
}

fun generateAutomaton(prefixTree: Tree,
                      vertexDegree: Int,
                      additionalTimersNumber: Int,
                      maxTotalEdges: Int,
                      inf: Int,
                      range: IntRange): MutableAutomaton? {
    for (statesNumber in range) {
        val maxActiveTimersCount = statesNumber * vertexDegree * (1 + additionalTimersNumber)
        writeDataIntoDzn(
            prefixTree,
            statesNumber,
            vertexDegree,
            additionalTimersNumber,
            maxActiveTimersCount,
            maxTotalEdges,
            inf)

        println("Checking $statesNumber states")
        val scanner = executeMinizinc()

        if (scanner == null) {
            println("Unsatisfiable for $statesNumber states")
        } else  {
            println("Satisfiable for $statesNumber states")

            return getAutomaton(
                prefixTree,
                statesNumber,
                vertexDegree,
                additionalTimersNumber,
                scanner).also { scanner.close() }
        }
    }
    return null
}

const val defaultVertexDegree = 10
const val defaultMaxTotalEdges = 20
const val defaultAdditionalTimersNumber = 0

data class ProgramTraces(val validTraces: List<Trace>, val invalidTraces: List<Trace>)

fun readTraces(scanner: Scanner, amount: Int, acceptable: Boolean): List<Trace> =
    List(amount) {
        val traceLength = scanner.nextInt()
        val records = List(traceLength) {
            Record(scanner.next(), scanner.nextInt())
        }
        normalize(Trace(records, acceptable))
    }

fun readTraces(consoleInfo: ConsoleInfo): ProgramTraces {
    val scanner = Scanner(consoleInfo.inputStream)
    val validTracesAmount = scanner.nextInt()
    val validTraces = readTraces(scanner, validTracesAmount, true)
    val invalidTracesAmount = scanner.nextInt()
    val invalidTraces = readTraces(scanner, invalidTracesAmount, false)
    return ProgramTraces(validTraces, invalidTraces).also { scanner.close() }
}

data class ConsoleInfo(val inputStream: InputStream,
                       val vertexDegree: Int,
                       val maxTotalEdges: Int,
                       val additionalTimersNumber: Int,
                       val range: IntRange)

fun<T> Map<String, List<String>>.getFirstArg(key: String,
                                             default: T,
                                             transform: (String) -> T?): T {
    return transform(this[key]?.let { it.firstOrNull() ?: return default } ?: return default) ?: default
}

fun parseConsoleArguments(args: Array<String>): ConsoleInfo {
    val map = mutableMapOf<String, MutableList<String>>()
    var lastList = mutableListOf<String>()
    for (str in args) {
        if (str.startsWith("-")) {
            lastList = mutableListOf()
            map[str] = lastList
        } else {
            lastList.add(str)
        }
    }
    return ConsoleInfo(
        map.getFirstArg("-s", System.`in`) { File(it).inputStream() },
        map.getFirstArg("-vd", defaultVertexDegree) { it.toInt() },
        map.getFirstArg("-mte", defaultMaxTotalEdges) { it.toInt() },
        map.getFirstArg("-atn", defaultAdditionalTimersNumber) { it.toInt() },
        map.getFirstArg("-n", 1..Int.MAX_VALUE) { val n = it.toInt(); n..n })
}

fun main(args: Array<String>) {
    val consoleInfo = parseConsoleArguments(args)
    val traces = readTraces(consoleInfo)
    val prefixTree = buildPrefixTree(traces.validTraces + traces.invalidTraces)
    prefixTree.createDotFile("prefixTree")

    val infinity = ((traces.invalidTraces + traces.validTraces).map {
        it.records.sumBy { it.time }
    }.max() ?: 0) + 2

    System.err.println("Infinity = $infinity")

    val automaton = generateAutomaton(
        prefixTree,
        consoleInfo.vertexDegree,
        consoleInfo.additionalTimersNumber,
        consoleInfo.maxTotalEdges,
        infinity,
        consoleInfo.range)

    if (automaton != null) {
        automaton.createDotFile("automaton")
        val (validVerdict, invalidVerdict) = automaton.checkAllTraces(traces)

        println("Checking results:")
        println("Valid traces:")
        println("Accepted traces: ${validVerdict.correct}")
        println("Unaccepted traces: ${validVerdict.incorrect}")
        println("Invalid traces:")
        println("Accepted traces: ${invalidVerdict.correct}")
        println("Unaccepted traces: ${invalidVerdict.incorrect}")
    }
}
