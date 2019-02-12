import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Paths
import java.util.*

data class Record(val name: String, val time: Int)

class Tree(val ways: Map<Record, Tree>)

class MutableTree(private val ways: MutableMap<Record, MutableTree> = mutableMapOf()) {
    fun toTree(): Tree = Tree(ways.mapValues { it.value.toTree() })

    fun addTrace(trace: Trace) {
        val next = ways.getOrPut(trace.firstOrNull() ?: return) { MutableTree() }
        next.addTrace(trace.subList(1, trace.size))
    }
}

typealias Timer = Int

data class Conditions(val label: String, val timeGuards: Map<Timer, IntRange>) {
    fun suit(label: String, timerManager: TimerManager) =
        label == this.label && timeGuards.all { timerManager[it.key] in it.value }
}

sealed class Either<T, E>
class ErrorContainer<T, E>(val error: E): Either<T, E>()
class AnswerContainer<T, E>(val answer: T): Either<T, E>()

class MutableAutomaton(
    val ways: MutableMap<Conditions, Pair<Set<Timer>, MutableAutomaton>> = mutableMapOf(),
    var final: Boolean = false,
    val name: String) {

    fun nextState(label: String, timerManager: TimerManager): Either<Pair<Set<Timer>, MutableAutomaton>, Error> {
        val possibleWays = ways.filterKeys { it.suit(label, timerManager) }.values.toList()
        if (possibleWays.size > 1) {
            return ErrorContainer(Error("There is more than one way to go"))
        }
        val possibleAutomaton = possibleWays.firstOrNull()
            ?: return ErrorContainer(Error("There is no way to go!"))
        return AnswerContainer(possibleAutomaton)
    }
}

typealias Trace = List<Record>

data class Edge<T>(val from: Int, val to: Int, val data: T)

fun buildPrefixTree(traces: Array<Trace>) =
    MutableTree().also { tree -> traces.forEach { tree.addTrace(it) } }.toTree()

data class Verdict(val correct: List<Trace>, val incorrect: List<Trace>)

class TimerManager {
    private val timer2Time = mutableMapOf<Timer, Int>()
    private var time = 0

    operator fun get(timer: Timer) = time - timer2Time.getOrPut(timer) { 0 }

    fun reset(timer: Timer) {
        timer2Time[timer] = time
    }

    fun rewind(curTime: Int) {
        time = curTime
    }
}

fun checkAllTraces(traces: Array<Trace>, automaton: MutableAutomaton): Verdict {
    val result = traces.groupBy {
        val timerManager = TimerManager()
        var state = automaton
        for (record in it) {
            timerManager.rewind(record.time)
            val possibleNext = state.nextState(record.name, timerManager)
            state = when (possibleNext) {
                is ErrorContainer -> {
                    println(possibleNext.error)
                    return@groupBy false
                }
                is AnswerContainer -> {
                    for (timer in possibleNext.answer.first) {
                        timerManager.reset(timer)
                    }
                    possibleNext.answer.second
                }
            }
        }
        state.final
    }
    return Verdict(result.getOrDefault(true, listOf()), result.getOrDefault(false, listOf()))
}

fun parseMinizincOutput(scanner: Scanner, statesNumber: Int, additionalTimersNumber: Int): MutableAutomaton {
    val finalCount = scanner.nextInt()
    val finals = setOf(*Array(finalCount) { scanner.nextInt() })
    val automatonStates = Array(statesNumber) { MutableAutomaton(name = "${it + 1}", final = finals.contains(it + 1)) }
    val edgeCount = scanner.nextInt()
    for (edge in 0 until edgeCount) {
        val from = scanner.nextInt()
        val to   = scanner.nextInt()
        val label = scanner.next()
        val conditions = Conditions(label, mapOf(*Array(additionalTimersNumber + 1) {
            val leftBorder = scanner.nextInt()
            val rightBorder = scanner.nextInt()
            it to leftBorder..rightBorder
        }))
        val resetNumber = scanner.nextInt()
        automatonStates[from - 1].ways[conditions] = Pair(
            setOf(*Array(resetNumber) { scanner.nextInt() }),
            automatonStates[to - 1])
    }
    return automatonStates[0]
}

data class AutomatonEdge(val from: String, val to: String, val conditions: Conditions, val resets: Set<Timer>)

fun createDotFile(automaton: MutableAutomaton) {
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
    visitAutomaton(mutableSetOf(), automaton)
    PrintWriter("graph.dot").apply {
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
                    resets.joinToString { "r(t$it)\\n" }
                }${
                    conditions.timeGuards.entries.
                        joinToString { "${it.value.first} <= t${it.key} <= ${it.value.last}\\n" }
                }\"]")
            }
        }
        println("}")
    }.flush()

    val dot = ProcessBuilder("dot", "-Tps", "graph.dot", "-o", "graph.ps").start()
    dot.waitFor()
    System.err.println(dot.errorStream.readAllBytes().toString(Charsets.UTF_8))
    dot.destroy()
}

fun getEdges(tree: Tree): List<Edge<Record>> {
    fun getEdges(list: MutableList<Edge<Record>>, tree: Tree, enumerator: () -> Int): Int {
        val number = enumerator()
        for ((record, internal) in tree.ways) {
            val childNumber = getEdges(list, internal, enumerator)
            list += Edge(number, childNumber, record)
        }
        return number
    }
    val list = mutableListOf<Edge<Record>>()
    var nextVertex = 1
    getEdges(list, tree) { nextVertex++ }
    return list
}

fun writeDataIntoDzn(tree: Tree, statesNumber: Int, vertexDegree: Int, additionalTimersNumber: Int) {
    val edges = getEdges(tree)
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("prefix_data.dzn").apply {
        println("statesNumber = $statesNumber;")
        println("edgeMaxNumber = $vertexDegree;")
        println("prefixTreeEdgesNumber = ${edges.size};")
        println("additionalTimersNumber = $additionalTimersNumber;")
        println("SYMBOLS = { ${symbols.joinToString()} };")
        println("labels = ${edges.map { it.data.name }};")
        println("prevVertex = ${edges.map { it.from }};")
        println("nextVertex = ${edges.map { it.to }};")
        println("times = ${edges.map { it.data.time }};")
    }.flush()
}

fun writeDataIntoTmpDzn(scanner: Scanner, tree: Tree, statesNumber: Int, vertexDegree: Int, additionalTimersNumber: Int) {
    val edges = getEdges(tree)
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("tmp.dzn").apply {
        println("statesNumber = $statesNumber;")
        println("edgeMaxNumber = $vertexDegree;")
        println("additionalTimersNumber = $additionalTimersNumber;")
        println("SYMBOLS = { ${symbols.joinToString()} };")
        while (true) {
            val nextLine = scanner.nextLine()
            if (!scanner.hasNextLine()) {
                break
            }
            println(nextLine)
        }
    }.flush()
}

fun executeMinizinc(tmpPrinter: (Scanner) -> Unit): Scanner? {
    val minizinc = ProcessBuilder("minizinc", "automaton_pref.mzn", "prefix_data.dzn", "-o", "tmp").start()
    minizinc.waitFor()
    System.err.println(minizinc.errorStream.readAllBytes().toString(Charsets.UTF_8))
    val scanner = Scanner(Paths.get("tmp").toFile())
    return when (scanner.hasNext("=====UNSATISFIABLE=====")) {
        false -> {
            tmpPrinter(scanner)
            val automatonPrinter = ProcessBuilder("minizinc", "automaton_printer.mzn", "tmp.dzn", "-o", "tmp1").start()
            automatonPrinter.waitFor()
            System.err.println(automatonPrinter.errorStream.readAllBytes().toString(Charsets.UTF_8))
            Scanner(Paths.get("tmp1").toFile()).also { automatonPrinter.destroy() }
        }
        else -> null
    }.also { minizinc.destroy() }
}

fun generateAutomaton(prefixTree: Tree, vertexDegree: Int, additionalTimersNumber: Int): MutableAutomaton {
    var statesNumber = 1
    while(true) {
        writeDataIntoDzn(prefixTree, statesNumber, vertexDegree, additionalTimersNumber)
        val scanner = executeMinizinc { writeDataIntoTmpDzn(it, prefixTree, statesNumber, vertexDegree, additionalTimersNumber) }
        when (scanner) {
            null -> {
                println("Unsatisfiable for $statesNumber states")
                statesNumber++
            }
            else -> return parseMinizincOutput(scanner, statesNumber, additionalTimersNumber)
        }
    }
}

const val defaultVertexDegree = 3
const val defaultAdditionalTimersNumber = 0

fun readTraces(consoleInfo: ConsoleInfo): Array<Trace> {
    val scanner = Scanner(consoleInfo.inputStream)
    val tracesAmount = scanner.nextInt()
    return Array(tracesAmount) {
        val traceLength = scanner.nextInt()
        Array(traceLength) {
            Record(scanner.next(), scanner.nextInt())
        }.toList()
    }
}

data class ConsoleInfo(val inputStream: InputStream)

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
    return ConsoleInfo(map["-s"]?.let {
        Paths.get(it.firstOrNull() ?: return@let System.`in`).toFile().inputStream()
    } ?: System.`in`)
}

fun main(args: Array<String>) {
    val consoleInfo = parseConsoleArguments(args)
    val traces: Array<Trace> = readTraces(consoleInfo)
    val prefixTree = buildPrefixTree(traces)
    val automaton = generateAutomaton(prefixTree, defaultVertexDegree, defaultAdditionalTimersNumber)
    createDotFile(automaton)
    val verdict = checkAllTraces(traces, automaton)
    println("Checking results: ")
    println("Accepted traces: ${verdict.correct}")
    println("Unaccepted traces: ${verdict.incorrect}")
}