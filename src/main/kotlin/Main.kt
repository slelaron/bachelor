import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Paths
import java.util.*

enum class Type { B, E }

data class Record(val name: String, val type: Type, val time: Int)

class Tree(val ways: Map<Record, Tree>)

class MutableTree(private val ways: MutableMap<Record, MutableTree> = mutableMapOf()) {
    fun toTree(): Tree = Tree(ways.mapValues { it.value.toTree() })

    fun addTrace(trace: Trace) {
        val next = ways.getOrPut(trace.firstOrNull() ?: return) { MutableTree() }
        next.addTrace(trace.subList(1, trace.size))
    }
}

typealias Timer = Int

data class Conditions(val label: String, val type: Type, val timeGuards: Map<Timer, IntRange>) {
    fun suit(label: String, type: Type, timerManager: TimerManager) =
        label == this.label && type == this.type && timeGuards.all { timerManager[it.key] in it.value }
}

sealed class Either<T, E>
class ErrorContainer<T, E>(val error: E): Either<T, E>()
class AnswerContainer<T, E>(val answer: T): Either<T, E>()

class MutableAutomaton(
    val ways: MutableMap<Conditions, Pair<Set<Timer>, MutableAutomaton>> = mutableMapOf(),
    var final: Boolean = false,
    val name: String) {

    fun nextState(label: String, type: Type, timerManager: TimerManager): Either<Pair<Set<Timer>, MutableAutomaton>, String> {
        val possibleWays = ways.filterKeys { it.suit(label, type, timerManager) }.values.toList()
        if (possibleWays.size > 1) {
            return ErrorContainer("There is more than one way to go")
        }
        val possibleAutomaton = possibleWays.firstOrNull()
            ?: return ErrorContainer("There is no way to go!")
        return AnswerContainer(possibleAutomaton)
    }
}

typealias Trace = List<Record>

data class Edge<T>(val from: Int, val to: Int, val data: T)

fun buildPrefixTree(traces: List<Trace>) =
    MutableTree().also { tree -> traces.forEach { tree.addTrace(it) } }.toTree()

data class AnnotatedTrace(val trace: Trace, val reason: String)

data class Verdict(val correct: List<Trace>, val incorrect: List<AnnotatedTrace>)

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

fun checkAllTraces(traces: List<Trace>, automaton: MutableAutomaton): Verdict {
    val result = traces.map {
        val timerManager = TimerManager()
        var state = automaton
        for (record in it) {
            timerManager.rewind(record.time)
            val possibleNext = state.nextState(record.name, record.type, timerManager)
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

fun checkAllTraces(traces: ProgramTraces, automaton: MutableAutomaton): Pair<Verdict, Verdict> =
        Pair(checkAllTraces(traces.validTraces, automaton), checkAllTraces(traces.invalidTraces, automaton))

fun parseMinizincOutput(scanner: Scanner, statesNumber: Int, additionalTimersNumber: Int): MutableAutomaton {
    val finalCount = scanner.nextInt()
    val finals = setOf(*Array(finalCount) { scanner.nextInt() })
    val automatonStates = Array(statesNumber) { MutableAutomaton(name = "${it + 1}", final = finals.contains(it + 1)) }
    val edgeCount = scanner.nextInt()
    for (edge in 0 until edgeCount) {
        val from = scanner.nextInt()
        val to   = scanner.nextInt()
        val label = scanner.next()
        val type = when (scanner.next()) {
            "E" -> Type.E
            "B" -> Type.B
            else -> throw IllegalStateException("Wrong output format")
        }

        val timerNumber = scanner.nextInt()
        val conditions = Conditions(label, type, mapOf(*Array(timerNumber) {
            val timer = scanner.nextInt()
            val leftBorder = scanner.nextInt()
            val rightBorder = scanner.nextInt()
            timer to leftBorder..rightBorder
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
                println("\tq$from -> q$to[label=\"${conditions.label}:${
                        if (conditions.type == Type.B) "B" else "E"
                    }\\n${
                    resets.joinToString("") { "r(t$it)\\n" }
                }${
                    conditions.timeGuards.entries.
                        joinToString("\\n") { "${it.value.first} <= t${it.key} <= ${it.value.last}" }
                }\"]")
            }
        }
        println("}")
    }.close()

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

fun writeDataIntoDzn(tree: Tree,
                     statesNumber: Int,
                     vertexDegree: Int,
                     additionalTimersNumber: Int,
                     maxActiveTimersCount: Int,
                     maxTotalEdges: Int) {
    val edges = getEdges(tree)
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("prefix_data.dzn").apply {
        println("statesNumber = $statesNumber;")
        println("edgeMaxNumber = $vertexDegree;")
        println("prefixTreeEdgesNumber = ${edges.size};")
        println("additionalTimersNumber = $additionalTimersNumber;")
        println("maxActiveTimersCount = $maxActiveTimersCount;")
        println("SYMBOLS = { ${symbols.joinToString()} };")
        println("labels = ${edges.map { it.data.name }};")
        println("types = ${edges.map { it.data.type }};")
        println("prevVertex = ${edges.map { it.from }};")
        println("nextVertex = ${edges.map { it.to }};")
        println("times = ${edges.map { it.data.time }};")
        println("maxTotalEdges = $maxTotalEdges;")
    }.close()
}

fun writeDataIntoTmpDzn(scanner: Scanner,
                        tree: Tree,
                        statesNumber: Int,
                        vertexDegree: Int,
                        additionalTimersNumber: Int) {
    val edges = getEdges(tree)
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("tmp.dzn").apply {
        println("statesNumber = $statesNumber;")
        println("edgeMaxNumber = $vertexDegree;")
        println("additionalTimersNumber = $additionalTimersNumber;")
        println("SYMBOLS = { ${symbols.joinToString()} };")
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
    return when (scanner.hasNext("=====UNSATISFIABLE=====") || output.startsWith("=====UNSATISFIABLE=====")) {
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
    writeDataIntoTmpDzn(scanner, prefixTree, statesNumber, vertexDegree, additionalTimersNumber)
    scanner.close()

    val automatonPrinter = ProcessBuilder(
        "minizinc",
        "automaton_printer.mzn",
        "tmp.dzn",
        "-o", "tmp1").start()
    automatonPrinter.waitFor()
    System.err.println(automatonPrinter.errorStream.readAllBytes().toString(Charsets.UTF_8))
    automatonPrinter.destroy()

    return parseMinizincOutput(Scanner(Paths.get("tmp1").toFile()), statesNumber, additionalTimersNumber)
}

fun generateAutomaton(prefixTree: Tree,
                      vertexDegree: Int,
                      additionalTimersNumber: Int,
                      maxTotalEdges: Int): MutableAutomaton {
    var statesNumber = 1
    while (true) {
        val maxActiveTimersCount = statesNumber * vertexDegree * (1 + additionalTimersNumber)
        writeDataIntoDzn(prefixTree, statesNumber, vertexDegree, additionalTimersNumber, maxActiveTimersCount, maxTotalEdges)

        println("Checking $statesNumber states")
        val scanner = executeMinizinc()

        if (scanner == null) {
            println("Unsatisfiable for $statesNumber states")
            statesNumber++
        } else  {
            println("Satisfiable for $statesNumber states")
            println("Starting moving maxActiveTimersCount")
            scanner.close()

            //var activeTimersNumber = 0
            var activeTimersNumber = maxActiveTimersCount
            while (true) {
                writeDataIntoDzn(prefixTree, statesNumber, vertexDegree, additionalTimersNumber, activeTimersNumber, maxTotalEdges)
                println("Checking $statesNumber states and $activeTimersNumber active timers")
                val scanner = executeMinizinc()
                if (scanner == null) {
                    println("Unsatisfiable for $statesNumber states and $activeTimersNumber active timers")
                    activeTimersNumber++
                } else {
                    println("Satisfiable for $statesNumber states and $activeTimersNumber active timers")
                    return getAutomaton(
                        prefixTree,
                        statesNumber,
                        vertexDegree,
                        additionalTimersNumber,
                        scanner)
                }
            }
        }
    }
}

const val defaultVertexDegree = 3
const val defaultMaxTotalEdges = 8
const val defaultAdditionalTimersNumber = 1

data class ProgramTraces(val validTraces: List<Trace>, val invalidTraces: List<Trace>)

fun readTraces(scanner: Scanner, amount: Int) =
        Array(amount) {
            val traceLength = scanner.nextInt()
            Array(traceLength) {
                Record(scanner.next(),
                    when (scanner.next()) {
                        "E" -> Type.E
                        "B" -> Type.B
                        else -> throw IllegalStateException("Invalid type of label")
                    }, scanner.nextInt())
            }.toList()
        }.toList()

fun readTraces(consoleInfo: ConsoleInfo): ProgramTraces {
    val scanner = Scanner(consoleInfo.inputStream)
    val validTracesAmount = scanner.nextInt()
    val validTraces = readTraces(scanner, validTracesAmount)
    val invalidTracesAmount = scanner.nextInt()
    val invalidTraces = readTraces(scanner, invalidTracesAmount)
    return ProgramTraces(validTraces, invalidTraces)
}

fun normalizeTrace(trace: Trace): Trace {
    val shiftedTrace = generateSequence { trace[0] }.asIterable()
    return (trace zip shiftedTrace).map { (f, s) -> Record(f.name, f.type, f.time - s.time) }
}

fun normalizeAllTraces(traces: ProgramTraces) =
    ProgramTraces(traces.validTraces.map { normalizeTrace(it) }, traces.invalidTraces.map { normalizeTrace(it) })

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
    val traces = normalizeAllTraces(readTraces(consoleInfo))
    val prefixTree = buildPrefixTree(traces.validTraces)
    val automaton = generateAutomaton(
        prefixTree,
        defaultVertexDegree,
        defaultAdditionalTimersNumber,
        defaultMaxTotalEdges)
    createDotFile(automaton)
    val (validVerdict, invalidVerdict) = checkAllTraces(traces, automaton)

    println("Checking results:")
    println("Valid traces:")
    println("Accepted traces: ${validVerdict.correct}")
    println("Unaccepted traces: ${validVerdict.incorrect}")
    println("Invalid traces:")
    println("Accepted traces: ${invalidVerdict.correct}")
    println("Unaccepted traces: ${invalidVerdict.incorrect}")
}