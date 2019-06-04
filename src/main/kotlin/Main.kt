import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Paths
import java.util.*

data class Record(val name: String, val time: Int)

open class Tree(open val ways: Map<Record, Tree>, open val acceptable: Boolean?)

class MutableTree(override val ways: MutableMap<Record, MutableTree> = mutableMapOf(),
                  override var acceptable: Boolean? = null): Tree(ways, acceptable) {
    operator fun plusAssign(trace: Trace) {
        val next = ways.getOrPut(trace.records.firstOrNull() ?: run {
            if (acceptable != null && acceptable != trace.acceptable) {
                throw IllegalStateException("Inconsistent traces")
            }
            acceptable = trace.acceptable
            return
        }) { MutableTree() }
        next += Trace(trace.records.subList(1, trace.records.size), trace.acceptable)
    }
}

typealias Timer = Int

data class Conditions(val label: String, val timeGuards: Map<Timer, IntRange>) {
    fun suit(label: String, timerManager: TimerManager) =
        label == this.label && timeGuards.all { timerManager[it.key] in it.value }
}

sealed class Either<out T, out E>
data class ErrorContainer<out T, out E>(val error: E): Either<T, E>()
data class AnswerContainer<out T, out E>(val answer: T): Either<T, E>()

fun<T, E, Q> Either<T, E>.map(f: (T) -> Q): Either<Q, E> =
    when (this) {
        is AnswerContainer -> AnswerContainer(f(answer))
        is ErrorContainer -> ErrorContainer(error)
    }

open class Automaton(
    open val ways: Map<Conditions, Pair<Set<Timer>, Automaton>>,
    open val final: Boolean?, open val name: String) {

    protected fun<T> Map<Conditions, Pair<Set<Timer>, T>>.nextState(label: String, timerManager: TimerManager): Either<Pair<Set<Timer>, T>, String> {
        val possibleWays = filterKeys { it.suit(label, timerManager) }.values.toList()
        if (possibleWays.size > 1) {
            return ErrorContainer("There is more than one way to go from $name: need={$label, $timerManager}")
        }
        val possibleAutomaton = possibleWays.firstOrNull()
            ?: return ErrorContainer("There is no way to go from $name: need={$label, $timerManager}}")
        return AnswerContainer(possibleAutomaton)
    }

    open operator fun get(label: String, timerManager: TimerManager) = ways.nextState(label, timerManager)

    override fun toString(): String {
        val (edges, states) = edgesAndStates
        val accStates = states.filter { it.final == true }
        val builder = StringBuilder()
        builder.
            appendln(states.size).
            appendln(states.joinToString(" ") { it.name }).
            appendln(accStates.size).
            appendln(accStates.joinToString(" ") { it.name }).
            appendln(edges.size)

        for (edge in edges) {
            builder.append("${edge.from.name} ${edge.to.name} ${edge.conditions.label} ${edge.conditions.timeGuards.size} ")
            for (guard in edge.conditions.timeGuards) {
                builder.append("${guard.key} ${guard.value.start} ${guard.value.endInclusive} ")
            }
            builder.append("${edge.resets.size} ").
                appendln(edge.resets.joinToString(" "))
        }
        return builder.toString()
    }
}

fun readAutomaton(scanner: Scanner): Automaton {
    val statesNumber = scanner.nextInt()
    val statesNames = List(statesNumber) { scanner.next() }
    val finalCount = scanner.nextInt()
    val finals = List(finalCount) { scanner.next() }.toSet()
    val automatonStates = List(statesNumber) {
        statesNames[it] to MutableAutomaton(name = statesNames[it], final = finals.contains(statesNames[it]))
    }.toMap()
    val edgeCount = scanner.nextInt()
    for (edge in 0 until edgeCount) {
        val from = automatonStates[scanner.next()] ?: throw Exception("No such state(from)")
        val to   = automatonStates[scanner.next()] ?: throw Exception("No such state(to)")
        val label = scanner.next()

        val timerNumber = scanner.nextInt()
        val conditions = Conditions(label, List(timerNumber) {
            val timer = scanner.nextInt()
            val leftBorder = scanner.nextInt()
            val rightBorder = scanner.nextInt()
            timer to leftBorder..rightBorder
        }.toMap())
        val resetNumber = scanner.nextInt()
        from.ways[conditions] = Pair(
            List(resetNumber) { scanner.nextInt() }.toSet(),
            to)
    }
    return automatonStates["q1"] ?: throw Exception("No start state")
}

class MutableAutomaton(
    override val ways: MutableMap<Conditions, Pair<Set<Timer>, MutableAutomaton>> = mutableMapOf(),
    override var final: Boolean? = null,
    override var name: String): Automaton(ways, final, name) {

    override operator fun get(label: String, timerManager: TimerManager) = ways.nextState(label, timerManager)
}

data class Trace(val records: List<Record>, val acceptable: Boolean) {
    override fun toString() =
        "${if (acceptable) "Ok" else "No"}: ${records.joinToString(" ") { a -> "(${a.name} ${a.time})" }}"
}

data class Edge<T>(val from: Int, val to: Int, val data: T)

fun normalize(rawTrace: Trace) =
        Trace(rawTrace.records.zipWithNext { a, b ->
            Record(b.name, b.time - a.time)
        }, rawTrace.acceptable) // plug until there are bad traces, after some time it doesn't need any more

fun buildPrefixTree(traces: Iterable<Trace>): Tree {
    val tree = MutableTree()
    for (trace in traces) {
        tree += trace
    }
    return tree
}

data class AnnotatedTrace(val trace: Trace, val reason: String)

data class Verdict(val correct: List<Trace>, val incorrect: List<AnnotatedTrace>)

class TimerManager {
    private val timer2Time = mutableMapOf<Timer, Int>()
    var global = 0
        set(new) {
            field = new.takeIf { it >= global } ?: throw IllegalStateException("New time value must be bigger than previous one")
        }

    operator fun get(timer: Timer) = global - timer2Time.getOrPut(timer) { 0 }

    fun reset(timer: Timer) {
        timer2Time[timer] = global
    }

    override fun toString() = "Manager(globalTime=$global, timer2time=$timer2Time)"
}

fun Automaton.checkAllTraces(traces: Iterable<Trace>, samplingDegree: Int? = null, inf: Int? = null): Verdict {
    val result = traces.map {
        val trace = if (samplingDegree != null) it.sample(samplingDegree, inf ?: traces.infinity()) else it
        val timerManager = TimerManager()
        var state = this
        for (record in trace.records) {
            timerManager.global += record.time
            val possibleNext = state[record.name, timerManager]
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
        AnnotatedTrace(it, if (state.final == true) "" else "Nonterminal state")
    }
    return Verdict(result.filter { it.reason == "" }.map { it.trace }, result.filter { it.reason != "" })
}

fun Automaton.checkAllTraces(traces: ProgramTraces): Pair<Verdict, Verdict> =
        Pair(checkAllTraces(traces.validTraces), checkAllTraces(traces.invalidTraces))

data class AutomatonEdge<T: Automaton>(val from: T, val to: T, val conditions: Conditions, val resets: Set<Timer>)

val Automaton.edgesAndStates: Pair<List<AutomatonEdge<Automaton>>, List<Automaton>>
    get() {
        val visited = mutableSetOf<String>()
        val states = mutableListOf<Automaton>()
        val edges = mutableListOf<AutomatonEdge<Automaton>>()
        fun Automaton.visitAutomaton() {
            visited += name
            states += this
            for ((key, value) in ways) {
                val nextState = value.second
                edges += AutomatonEdge(this, nextState, key, value.first)
                if (nextState.name !in visited) {
                    nextState.visitAutomaton()
                }
            }
        }
        visitAutomaton()
        return edges to states
    }

fun Automaton.createDotFile(fileName: String, inf: Int = Int.MAX_VALUE) {
    val (edges, states) = edgesAndStates
    PrintWriter("$fileName.dot").apply {
        println("digraph \"$fileName\" {")
        for (state in states) {
            with(state) {
                println("\t$name[label=$name${
                    when (final) {
                        true -> " shape=doublecircle"
                        else -> ""
                    }
                }]")
            }
        }
        for (edge in edges) {
            with(edge) {
                println("\t${from.name} -> ${to.name}[label=\"${conditions.label}\\n${
                    resets.joinToString("") { "r(t$it)\\n" }
                }${
                    conditions.timeGuards.entries.
                        mapNotNull { 
                            when {
                                it.value.first == 0 && it.value.last == inf -> null
                                it.value.last == inf -> "[${it.value.first} <= t${it.key}]"
                                it.value.first == 0 -> "[t${it.key} <= ${it.value.last}]"
                                else -> "[${it.value.first} <= t${it.key} <= ${it.value.last}]" 
                            }
                        }.joinToString("\\n")
                }\"]")
            }
        }
        println("}")
        flush()
    }.close()

    val dot = ProcessBuilder("dot", "-Tps", "$fileName.dot", "-o", "$fileName.ps").start()
    dot.waitFor()
    System.err.println(dot.errorStream.readAllBytes().toString(Charsets.UTF_8))
    dot.destroy()
}

fun Tree.createDotFile(name: String) {
    val (edges, vertexes) = this.edgesAndVertexes
    PrintWriter("$name.dot").apply {
        println("digraph $name {")
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

fun Environment.writeDataIntoDzn(): Boolean {
    val (edges, vertexes) = prefixTree?.edgesAndVertexes ?: return false
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("prefix_data.dzn").apply {
        println("V = $statesNumber;")
        println("E = $vertexDegree;")
        println("M = ${edges.size};")
        println("T = $timersNumber;")
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
        println("inf = ${if (samplingDegree != null) samplingDegree - 1 else infinity};")
        flush()
    }.close()
    return true
}

fun Environment.writeDataIntoTmpDzn(scanner: Scanner): Boolean {
    val (edges, _) = prefixTree?.edgesAndVertexes ?: return false
    val symbols = edges.map { it.data.name }.toSet()
    PrintWriter("tmp.dzn").apply {
        println("V = $statesNumber;")
        println("E = $vertexDegree;")
        println("T = $timersNumber;")
        println("S = { ${symbols.joinToString()} };")
        while (true) {
            if (!scanner.hasNextLine() ||
                scanner.hasNext("----------") ||
                scanner.hasNext("==========")) {
                break
            }
            println(scanner.nextLine())
        }
        flush()
    }.close()
    return true
}

fun Environment.executeMinizinc(): Scanner? {
    val minizinc = ProcessBuilder(
        "minizinc",
        solution,
        "prefix_data.dzn",
        "--solver",
        solver,
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

fun Environment.getAutomaton(scanner: Scanner): Automaton? {
    if (!writeDataIntoTmpDzn(scanner)) return null
    scanner.close()

    val automatonPrinter = ProcessBuilder(
        "minizinc",
        "automaton_printer.mzn",
        "tmp.dzn",
        "-o", "tmp1").start()
    automatonPrinter.waitFor()
    System.err.println(automatonPrinter.errorStream.readAllBytes().toString(Charsets.UTF_8))
    automatonPrinter.destroy()

    return readAutomaton(Scanner(Paths.get("tmp1").toFile()))
}

fun Environment.generateAutomaton(): Automaton? {
    if (!writeDataIntoDzn()) return null

    return when (val scanner = executeMinizinc()) {
        null -> {
            System.err.println("no: $this")
            null
        }
        else -> {
            System.err.println("OK: $this")
            getAutomaton(scanner).also { scanner.close() }
        }
    }
}

const val defaultTimersNumber = 1

data class ProgramTraces(val validTraces: List<Trace>, val invalidTraces: List<Trace>) {
    override fun toString(): String {
        val builder = StringBuilder()
        builder.appendln(validTraces.size)
        for ((records, _) in validTraces) {
            builder.appendln(records.size).
                    appendln(records.joinToString("\n") { "${it.name} ${it.time}" })
        }
        builder.appendln(invalidTraces.size)
        for ((records, _) in invalidTraces) {
            builder.appendln(records.size).
                appendln(records.joinToString("\n") { "${it.name} ${it.time}" })
        }
        return builder.toString()
    }

    fun toVerwer(): String {
        val traces = validTraces + invalidTraces
        val labels = buildPrefixTree(traces).labels().sorted()
        val label2Number = labels.mapIndexed { index, s -> s to index }.toMap()
        val builder = StringBuilder()
        builder.appendln("${traces.size} ${labels.size}")
        for (trace in traces) {
            builder.append("${if (trace.acceptable) 1 else 0} ${trace.records.size} ").
                appendln(trace.records.joinToString("  ") { "${
                    label2Number[it.name] ?: throw Exception("Verwer convert Error")
                } ${it.time}" })
        }
        return builder.toString()
    }
}

fun readTraces(scanner: Scanner, amount: Int, acceptable: Boolean): List<Trace> =
    List(amount) {
        val traceLength = scanner.nextInt()
        val records = List(traceLength) {
            Record(scanner.next(), scanner.nextInt())
        }
        Trace(records, acceptable)
    }

fun readTraces(inputStream: InputStream): ProgramTraces {
    val scanner = Scanner(inputStream)
    val validTracesAmount = scanner.nextInt()
    val validTraces = readTraces(scanner, validTracesAmount, true)
    val invalidTracesAmount = scanner.nextInt()
    val invalidTraces = readTraces(scanner, invalidTracesAmount, false)
    return ProgramTraces(validTraces, invalidTraces).also { scanner.close() }
}

data class ConsoleInfo(val inputStream: InputStream,
                       val vertexDegree: Int?,
                       val maxTotalEdges: Int?,
                       val timersNumber: Int,
                       val range: IntRange,
                       val helpMessage: String)

inline fun<T> Map<String, List<String>>.getFirstArg(keys: Iterable<String>,
                                                    default: T,
                                                    transform: (List<String>) -> T?): T {
    return transform(keys.mapNotNull { this[it] }.
        firstOrNull() ?: return default) ?: default
}

fun parseConsoleArguments(args: Array<String>): Map<String, List<String>> {
    val arg2Val = mutableListOf<Pair<String, MutableList<String>>>()
    for (str in args) {
        if (str.startsWith("-")) {
            arg2Val += str to mutableListOf()
        } else {
            arg2Val.lastOrNull()?.second?.add(str)
        }
    }
    return arg2Val.toMap()
}

fun parseConsoleArgumentsMain(args: Array<String>): ConsoleInfo {
    val map = parseConsoleArguments(args)
    return ConsoleInfo(
        map.getFirstArg(listOf("-s", "--source"), System.`in`) { Paths.get(it[0]).toFile().inputStream() },
        map.getFirstArg(listOf("-vd", "--vertexDegree"), null) { it[0].toInt() },
        map.getFirstArg(listOf("-mte", "--maxTotalEdges"), null) { it[0].toInt() },
        map.getFirstArg(listOf("-tn", "--timersNumber"), defaultTimersNumber) { it[0].toInt() },
        map.getFirstArg(listOf("-n", "--number"), 1..Int.MAX_VALUE) { val n = it[0].toInt(); n..n },
        map.getFirstArg(listOf("-h", "--help"), "") { helpMain })
}

fun Iterable<Trace>.infinity() = map { trace ->
    trace.records.sumBy { it.time }
}.max() ?: 0

fun Iterable<Trace>.labels() = flatMap { trace ->
    trace.records.map { it.name }
}.distinct()

fun Tree.infinity(start: Int = 0): Int = ways.map { (record, to) ->
    to.infinity(start + record.time)
}.max() ?: start

fun Tree.labels(): Set<String> = ways.flatMap { (record, to) ->
    to.labels() + record.name
}.toSet()

const val helpMain = """Hay everyone who want to use this DTA builder!
You should give samples to the program in following format (TAB symbols are unnecessary):
<P = POSITIVE SAMPLES NUMBER>
    <LP_1 = POSITIVE SAMPLE_1 LENGTH>
        <POSITIVE LABEL_1_1> <POSITIVE DELAY_1_1>
        <POSITIVE LABEL_1_2> <POSITIVE DELAY_1_2>
        ...
        <POSITIVE LABEL_1_<LP_1>> <POSITIVE DELAY_1_<LP_1>>
    <LP_2 = POSITIVE SAMPLE_2 LENGTH>
        <POSITIVE LABEL_2_1> <POSITIVE DELAY_2_1>
        <POSITIVE LABEL_2_2> <POSITIVE DELAY_2_2>
        ...
        <POSITIVE LABEL_2_<LP_2>> <POSITIVE DELAY_2_<LP_2>>
    ...
    <LP_P = POSITIVE SAMPLE_P LENGTH>
        <POSITIVE LABEL_P_1> <POSITIVE DELAY_P_1>
        <POSITIVE LABEL_P_2> <POSITIVE DELAY_P_2>
        ...
        <POSITIVE LABEL_P_<LP_P>> <POSITIVE DELAY_P_<LP_P>>
<N = NEGATIVE SAMPLES NUMBER>
    <LN_1 = NEGATIVE SAMPLE_1 LENGTH>
        <NEGATIVE LABEL_1_1> <NEGATIVE DELAY_1_1>
        <NEGATIVE LABEL_1_2> <NEGATIVE DELAY_1_2>
        ...
        <NEGATIVE LABEL_1_<LN_1>> <NEGATIVE DELAY_1_<LN_1>>
    <LN_2 = NEGATIVE SAMPLE_2 LENGTH>
        <NEGATIVE LABEL_2_1> <NEGATIVE DELAY_2_1>
        <NEGATIVE LABEL_2_2> <NEGATIVE DELAY_2_2>
        ...
        <NEGATIVE LABEL_2_<LN_2>> <NEGATIVE DELAY_2_<LN_2>>
    ...
    <LN_N = NEGATIVE SAMPLE_N LENGTH>
        <NEGATIVE LABEL_N_1> <NEGATIVE DELAY_N_1>
        <NEGATIVE LABEL_N_2> <NEGATIVE DELAY_N_2>
        ...
        <NEGATIVE LABEL_N_<LN_N>> <NEGATIVE DELAY_N_<LN_N>>
We provide you usage of following flags:
    (-s | --source) <PATH> - use your own <PATH> to samples.
    (-vd | --vertexDegree) <NUMBER> - computed automaton's vertex degree will be <NUMBER> at most. By default = statesNumber * labelsNumber.
    (-mte | --maxTotalEdges) <NUMBER> - computed automaton will have <NUMBER> edges at most. By default = statesNumber * vertexDegree.
    (-tn | --timersNumber) <NUMBER> - computed automaton will use <NUMBER> timers at most. By default = $defaultTimersNumber.
    (-n | --number) <NUMBER> - program will check possibility to build automaton with <NUMBER> states.
    (-h | --help) - program will print help message to you.
"""

fun main(args: Array<String>) {
    val consoleInfo = parseConsoleArgumentsMain(args)
    print(consoleInfo.helpMessage)

    val traces = readTraces(consoleInfo.inputStream)
    val prefixTree = buildPrefixTree(traces.validTraces + traces.invalidTraces)
    prefixTree.createDotFile("prefixTree")

    val automaton = mainStrategy(
        traces = traces.validTraces + traces.invalidTraces,
        vertexDegree = consoleInfo.vertexDegree,
        timersNumber = consoleInfo.timersNumber,
        maxTotalEdges = consoleInfo.maxTotalEdges,
        range = consoleInfo.range)

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
