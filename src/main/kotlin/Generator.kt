import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Paths
import kotlin.random.Random
import kotlin.streams.asSequence

class EdgeBuilder(var from: MutableAutomaton,
                  var to: MutableAutomaton,
                  var label: String,
                  val guards: Map<Timer, IntRange> = mutableMapOf(),
                  val resets: MutableSet<Timer> = mutableSetOf(),
                  val splitAt: MutableSet<Int> = mutableSetOf())

interface AutomatonGenerator: Iterable<Automaton>

class AutomatonGeneratorOneTimer(val statesNumber: Int,
                                 val splitsNumber: Int,
                                 val timeUpperBound: Int,
                                 val labels: List<String>,
                                 val resetProbability: Double = 0.0): AutomatonGenerator {
    override fun iterator() = object: Iterator<Automaton> {
        fun generate(): Automaton {
            val timer = 0
            val garbage = MutableAutomaton(name = "q0")
            val states = List(statesNumber) {
                MutableAutomaton(name = "q${it + 1}", final = Random.nextBoolean())
            }
            val possibleEdges = states.flatMap { i ->
                labels.map { EdgeBuilder(i, garbage, it) }
            }
            for (i in 0 until splitsNumber) {
                val edge = possibleEdges.random()
                val time = (0 until timeUpperBound).random()
                edge.splitAt += time
            }
            val dividedEdges = possibleEdges.flatMap { edge ->
                listOf(*edge.splitAt.toTypedArray(), Int.MAX_VALUE, -1).sorted().zipWithNext { a, b ->
                    EdgeBuilder(edge.from, edge.to, edge.label, mutableMapOf(timer to ((a + 1)..b)))
                }
            }
            for (edge in dividedEdges) {
                edge.to = states.random()
                if (Random.nextDouble() < resetProbability) {
                    edge.resets += timer
                }
            }
            for (edge in dividedEdges) {
                edge.from.ways[Conditions(edge.label, edge.guards)] = edge.resets to edge.to
            }
            return states[0]
        }

        override fun next(): Automaton {
            while (true) {
                val automaton = generate()
                val (_, states) = automaton.edgesAndStates
                if (states.any { it.final == true } && states.any { it.final == false } && states.size == statesNumber) {
                    return automaton
                }
            }
        }

        override fun hasNext() = true
    }
}

class PathGenerator(val automaton: Automaton,
                    val timeUpperBound: Int,
                    val stopProbability: Double,
                    val labels: List<String>): Iterable<Trace> {
    override fun iterator() = object: Iterator<Trace> {
        override fun hasNext() = true

        override fun next(): Trace {
            var state = automaton
            val records = mutableListOf<Record>()
            val timerManager = TimerManager()
            while (Random.nextDouble() > stopProbability) {
                val now = Record(labels.random(), (0..timeUpperBound).random())
                timerManager.global += now.time
                val (resets, next) =
                    when (val result = state[now.name, timerManager]) {
                        is ErrorContainer -> throw IllegalStateException(result.error)
                        is AnswerContainer -> result.answer
                    }
                for (timer in resets) {
                    timerManager.reset(timer)
                }
                state = next
                records += now
            }
            return Trace(records, state.final == true)
        }
    }
}

const val defaultNumberOfStates = 3
const val defaultSplitsNumber = 6
const val defaultTrainTraceNumber = 1000
const val defaultTestTraceNumber = 1000
const val defaultLabelsNumber = 2
const val defaultAutomatonTimeUpperBound = 50
const val defaultTraceTimeUpperBound = 50
const val defaultResetProbability = 1.0
const val defaultStopProbability = 0.1

const val helpGenerator = """Hay everyone who want to generate tests!
We provide you usage of following flags:
    (-t | --test) <NUMBER> - test you want to regenerate. Otherwise first free number will be chosen.
    (-n | --number) <NUMBER> - random automaton will have such number of states. By default: $defaultNumberOfStates.
    (-s | --splits) <NUMBER> - random automaton will have such number of splits. By default: $defaultSplitsNumber.
    (-l | --labels) <NUMBER> - random automaton will have such number of labels (max = 26). By default: $defaultLabelsNumber.
    (-rp | --resetProbability) <REAL> - random automaton random edge will reset random timer with such probability. By default: $defaultResetProbability.
    (-atb | --automatonTimeBound) <NUMBER> - random automaton will have such time upper bound. By default: $defaultAutomatonTimeUpperBound.
    (-ttb | --traceTimeBound) <NUMBER> - random traces will have such time upper bound. By default: $defaultTraceTimeUpperBound.
    (-tn | --trainNumber) <NUMBER> - train set will have such number of traces. By default: $defaultTrainTraceNumber.
    (-cn | --checkNumber) <NUMBER> - test set will have such number of traces. By default: $defaultTestTraceNumber.
    (-sp | --stopProbability) <REAL> - trace will have such probability to end with such length. By default: $defaultStopProbability
    (-h | --help) - program will print help message to you.
"""

data class GenerateInfo(val test: Int,
                        val statesNumber: Int,
                        val splitsNumber: Int,
                        val labels: List<String>,
                        val resetProbability: Double,
                        val automatonTimeUpperBound: Int,
                        val traceTimeUpperBound: Int,
                        val trainNumber: Int,
                        val testNumber: Int,
                        val stopProbability: Double,
                        val help: String)

fun parseConsoleArgumentsGenerator(args: Array<String>): GenerateInfo {
    val map = parseConsoleArguments(args)
    return GenerateInfo(
        map.getFirstArg(listOf("-t", "--test"), takeEmpty(DIR, PREFIX)) { it[0].toInt() },
        map.getFirstArg(listOf("-n", "--number"), defaultNumberOfStates) { it[0].toInt() },
        map.getFirstArg(listOf("-s", "--splits"), defaultSplitsNumber) { it[0].toInt() },
        map.getFirstArg(listOf("-l", "--labels"), defaultLabelsNumber) { it[0].toInt() }.let { ('a'..'z').take(it).map { c -> c.toString() } },
        map.getFirstArg(listOf("-rp", "--resetProbability"), defaultResetProbability) { it[0].toDouble() },
        map.getFirstArg(listOf("-atb", "--automatonTimeBound"), defaultAutomatonTimeUpperBound) { it[0].toInt() },
        map.getFirstArg(listOf("-ttb", "--traceTimeBound"), defaultTraceTimeUpperBound) { it[0].toInt() },
        map.getFirstArg(listOf("-tn", "--trainNumber"), defaultTrainTraceNumber) { it[0].toInt() },
        map.getFirstArg(listOf("-cn", "--checkNumber"), defaultTestTraceNumber) { it[0].toInt() },
        map.getFirstArg(listOf("-sp", "--stopProbability"), defaultStopProbability) { it[0].toDouble() },
        map.getFirstArg(listOf("-h", "--help"), "") { helpGenerator })
}

const val DIR = "tests_1"
const val PREFIX = "test"

fun takeEmpty(startDirectory: String, directory: String): Int {
    val testsDir = Paths.get(startDirectory)
    if (Files.notExists(testsDir)) {
        Files.createDirectory(testsDir)
    }
    val usedNumbers = Files.walk(testsDir, 1).asSequence().mapNotNull {path ->
        path.let {
            "^$startDirectory/$directory(\\d+)\$".toRegex().find(it.toString())?.destructured?.let {(result) ->
                result.toIntOrNull()
            }
        }
    }.toSet()

    return (1..Int.MAX_VALUE).first {it !in usedNumbers }
}


fun main(args: Array<String>) {
    val generateInfo = parseConsoleArgumentsGenerator(args)
    print(generateInfo.help)
    if (generateInfo.help != "") return

    val testDirName = "$DIR/$PREFIX${generateInfo.test}"
    val testDir = Paths.get(testDirName)
    if (Files.exists(testDir)) {
        testDir.toFile().deleteRecursively()
    }
    Files.createDirectory(testDir)

    val generator = AutomatonGeneratorOneTimer(
        statesNumber = generateInfo.statesNumber,
        splitsNumber = generateInfo.splitsNumber,
        timeUpperBound = generateInfo.automatonTimeUpperBound,
        labels = generateInfo.labels,
        resetProbability = generateInfo.resetProbability)

    val automaton = generator.first()
    val pathGenerator = PathGenerator(
        automaton = automaton,
        timeUpperBound = generateInfo.traceTimeUpperBound,
        stopProbability = generateInfo.stopProbability,
        labels = generateInfo.labels)

    val train = pathGenerator.take(generateInfo.trainNumber)
    val (trainCorrect, trainIncorrect) = train.partition { it.acceptable }
    val test = pathGenerator.take(generateInfo.testNumber)
    val (testCorrect, testIncorrect) = test.partition { it.acceptable }
    PrintWriter("$testDirName/train").apply {
        println(ProgramTraces(trainCorrect, trainIncorrect))
        flush()
    }.close()
    PrintWriter("$testDirName/test").apply {
        println(ProgramTraces(testCorrect, testIncorrect))
        flush()
    }.close()
    PrintWriter("$testDirName/automaton").apply {
        println(automaton)
        flush()
    }.close()
    automaton.createDotFile("$testDirName/automaton")
    PrintWriter("$testDirName/info").apply {
        println("states number = ${generateInfo.statesNumber}")
        println("splits number = ${generateInfo.splitsNumber}")
        println("labels = ${generateInfo.labels.joinToString(", ", prefix = "[", postfix = "]") }")
        println("reset probability = ${generateInfo.resetProbability}")
        println("automaton time upper bound = ${generateInfo.automatonTimeUpperBound}")
        println("traces time upper bound = ${generateInfo.traceTimeUpperBound}")
        println("train trace number = ${generateInfo.trainNumber}")
        println("test trace number = ${generateInfo.testNumber}")
        println("stop probability = ${generateInfo.stopProbability}")
        flush()
    }.close()
    PrintWriter("$testDirName/info_machine").apply {
        println(generateInfo.statesNumber)
        println(generateInfo.splitsNumber)
        println("${generateInfo.labels.size} ${generateInfo.labels.joinToString(" ")}")
        println(generateInfo.resetProbability)
        println(generateInfo.automatonTimeUpperBound)
        println(generateInfo.traceTimeUpperBound)
        println(generateInfo.trainNumber)
        println(generateInfo.testNumber)
        println(generateInfo.stopProbability)
        flush()
    }.close()
}
