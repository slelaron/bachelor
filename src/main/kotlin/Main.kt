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

data class Conditions(val label: String, val type: Type?, val timeGuards: Map<Timer, IntRange>) {
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

    fun nextState(label: String,
                  type: Type,
                  timerManager: TimerManager): Either<Pair<Set<Timer>, MutableAutomaton>, String> {
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

fun MutableAutomaton.checkAllTraces(traces: List<Trace>): Verdict {
    val result = traces.map {
        val timerManager = TimerManager()
        var state = this
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
        val type = when (scanner.next()) {
            "E" -> Type.E
            "B" -> Type.B
            else -> throw IllegalStateException("Wrong output format")
        }

        val timerNumber = scanner.nextInt()
        val conditions = Conditions(label, type, List(timerNumber) {
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
                println("\tq$from -> q$to[label=\"${conditions.label}${
                        when (conditions.type) {
                            null -> ""
                            Type.B -> ":B"
                            Type.E -> ":E"
                        }
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

    val dot = ProcessBuilder("dot", "-Tps", "$name.dot", "-o", "$name.ps").start()
    dot.waitFor()
    System.err.println(dot.errorStream.readAllBytes().toString(Charsets.UTF_8))
    dot.destroy()
}

fun Tree.createDotFile(name: String) {
    var vertexNumber = 1
    fun Tree.convert(automaton: MutableAutomaton): MutableAutomaton {
        if (ways.isEmpty()) {
            automaton.final = true
        }
        for ((record, next) in ways) {
            val nxt = next.convert(MutableAutomaton(name = "${vertexNumber++}"))
            val condition = Conditions("${record.name}:${record.type}, ${record.time}", null, mapOf())
            automaton.ways[condition] = setOf<Timer>() to nxt
        }
        return automaton
    }

    convert(MutableAutomaton(name = "${vertexNumber++}")).createDotFile(name)
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
                      range: IntRange): MutableAutomaton? {
    for (statesNumber in range) {
        val maxActiveTimersCount = statesNumber * vertexDegree * (1 + additionalTimersNumber)
        writeDataIntoDzn(
            prefixTree,
            statesNumber,
            vertexDegree,
            additionalTimersNumber,
            maxActiveTimersCount,
            maxTotalEdges)

        println("Checking $statesNumber states")
        val scanner = executeMinizinc()

        if (scanner == null) {
            println("Unsatisfiable for $statesNumber states")
        } else  {
            println("Satisfiable for $statesNumber states")
            /*println("Starting moving maxActiveTimersCount")
            scanner.close()*/

            //var activeTimersNumber = 0
            //var activeTimersNumber = maxActiveTimersCount
            /*while (true) {
                writeDataIntoDzn(
                    prefixTree,
                    statesNumber,
                    vertexDegree,
                    additionalTimersNumber,
                    activeTimersNumber,
                    maxTotalEdges)
                println("Checking $statesNumber states and $activeTimersNumber active timers")
                val secondScanner = executeMinizinc()
                if (secondScanner == null) {
                    println("Unsatisfiable for $statesNumber states and $activeTimersNumber active timers")
                    activeTimersNumber++
                } else {
                    println("Satisfiable for $statesNumber states and $activeTimersNumber active timers")
                    return getAutomaton(
                        prefixTree,
                        statesNumber,
                        vertexDegree,
                        additionalTimersNumber,
                        secondScanner).also { secondScanner.close() }
                }
            }*/

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

const val defaultVertexDegree = 3
const val defaultMaxTotalEdges = 20
const val defaultAdditionalTimersNumber = 1

data class ProgramTraces(val validTraces: List<Trace>, val invalidTraces: List<Trace>)

fun readTraces(scanner: Scanner, amount: Int) =
        List(amount) {
            val traceLength = scanner.nextInt()
            List(traceLength) {
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
    return ProgramTraces(validTraces, invalidTraces).also { scanner.close() }
}

fun normalizeTrace(trace: Trace): Trace {
    val infSequence = generateSequence { trace[0] }.asIterable()
    return (trace zip infSequence).map { (f, s) -> Record(f.name, f.type, f.time - s.time) }
}

fun normalizeAllTraces(traces: ProgramTraces) =
    ProgramTraces(traces.validTraces.map { normalizeTrace(it) }, traces.invalidTraces.map { normalizeTrace(it) })

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
        map.getFirstArg("-s", System.`in`) { Paths.get(it).toFile().inputStream() },
        map.getFirstArg("-vd", defaultVertexDegree) { it.toInt() },
        map.getFirstArg("-mte", defaultMaxTotalEdges) { it.toInt() },
        map.getFirstArg("-atn", defaultAdditionalTimersNumber) { it.toInt() },
        map.getFirstArg("-n", 1..Int.MAX_VALUE) { val n = it.toInt(); n..n })
}

fun main(args: Array<String>) {
    val consoleInfo = parseConsoleArguments(args)
    val traces = normalizeAllTraces(readTraces(consoleInfo))
    val prefixTree = buildPrefixTree(traces.validTraces)
    prefixTree.createDotFile("prefixTree")

    val automaton = generateAutomaton(
        prefixTree,
        consoleInfo.vertexDegree,
        consoleInfo.additionalTimersNumber,
        consoleInfo.maxTotalEdges,
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
