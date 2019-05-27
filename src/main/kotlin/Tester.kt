import java.io.File
import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Paths
import kotlin.random.Random

data class Environment(
    val solution: String,
    val solver: String,
    val prefixTree: Tree,
    val statesNumber: Int,
    val vertexDegree: Int,
    val maxTotalEdges: Int,
    val timersNumber: Int,
    val infinity: Int,
    val maxActiveTimersCount: Int
) {
    override fun toString() =
            "{ solution: $solution, solver: $solver, states: $statesNumber, infinity: $infinity, " +
                    "vertex degree: $vertexDegree, edges: $maxTotalEdges, timers: $timersNumber, " +
                    "active timers: $maxActiveTimersCount }"
}

fun decrease(start: Environment, startAutomaton: Automaton, until: Environment.() -> Boolean,
             transformer: Environment.(Automaton) -> Environment): Pair<Environment, Automaton> {
    var environment = start
    var automaton = startAutomaton
    while (environment.until()) {
        val new = environment.transformer(automaton)
        when (val newAutomaton = new.generateAutomaton()) {
            null -> return environment to automaton
            else -> {
                environment = new
                automaton = newAutomaton
            }
        }
    }
    return environment to automaton
}

fun Automaton.vertexDegree(): Int {
    val used = mutableSetOf<Automaton>()
    var max = 0
    fun Automaton.visit() {
        used += this
        max = maxOf(max, ways.size)
        for ((_, automaton) in ways.values) {
            if (automaton !in used) automaton.visit()
        }
    }
    visit()
    return max
}

fun mainStrategy(prefixTree: Tree,
                 timersNumber: Int,
                 range: IntRange = 1..Int.MAX_VALUE,
                 solution: String = "automaton_cbs.mzn",
                 solver: String  = "org.chuffed.chuffed",
                 vertexDegree: Int? = null,
                 maxTotalEdges: Int? = null,
                 maxActiveTimersCount: Int? = null,
                 infinity: Int = prefixTree.infinity(),
                 needMinimize: Boolean = false): Automaton? {
    val labels = prefixTree.labels().count()
    var automaton: Automaton?
    for (statesNumber in range) {
        val theVertexDegree = vertexDegree ?: statesNumber * labels
        val theMaxTotalEdges = maxTotalEdges ?: (theVertexDegree * statesNumber)
        val theMaxActiveTimersCount = maxActiveTimersCount ?: (theMaxTotalEdges * timersNumber)
        val environment = Environment(
            solution,
            solver,
            prefixTree,
            statesNumber,
            theVertexDegree,
            theMaxTotalEdges,
            timersNumber,
            infinity,
            theMaxActiveTimersCount)
        automaton = environment.generateAutomaton()
        if (automaton != null) {
            return if (needMinimize) {
                val (env0, aut0) = decrease(environment, automaton, { this.vertexDegree > 1 }) {
                    copy(vertexDegree = it.vertexDegree() - 1)
                }
                val (env1, aut1) = decrease(env0, aut0, { this.maxTotalEdges > 1 }) {
                    val (edges, _) = it.edgesAndStates
                    copy(maxTotalEdges = edges.size - 1)
                }
                val (_, aut2) = decrease(env1, aut1, { this.maxActiveTimersCount > 1 }) {
                    val (edges, _) = it.edgesAndStates
                    val activeTimers = edges.sumBy { e -> e.conditions.timeGuards.size }
                    copy(maxActiveTimersCount = activeTimers - 1)
                }
                aut2
            }
            else automaton
        }
    }
    return null
}

fun fMeasure(answers: List<List<Int>>): Double {
    if (answers.any { a -> answers.firstOrNull()?.let { it.size != a.size } == true })
        throw IllegalStateException("Wrong matrix")
    val n = answers.size
    val m = answers.firstOrNull()?.size ?: 0
    var weightedPrecision = 0.0
    var weightedRecall = 0.0
    val global = answers.sumByDouble { it.sum().toDouble() }
    for (i in 0 until n) {
        val rowSum = (0 until m).sumBy { answers[i][it] }
        val columnSum = (0 until m).sumBy { answers[it][i] }
        val precision = if (rowSum != 0) answers[i][i].toDouble() / rowSum else 0.0
        val recall = if (columnSum != 0) answers[i][i].toDouble() / columnSum else 0.0
        weightedPrecision += precision * rowSum
        weightedRecall += recall * rowSum
    }
    weightedPrecision /= global
    weightedRecall /= global
    return 2 * weightedPrecision * weightedRecall / (weightedPrecision + weightedRecall)
}

fun trainAutomaton(train: List<Trace>,
                   timersNumber: Int,
                   infinity: Int = train.infinity()): Automaton {
    /*val trainSet = mutableSetOf<Trace>()
    var automaton: Automaton = MutableAutomaton(name = "q0")
    var minimized = false
    while (true) {
        val verdict = automaton.checkAllTraces(train)
        val correct = verdict.correct.toSet()
        val incorrect = verdict.incorrect.map { it.trace }.toSet()
        val trace = train.firstOrNull { if (it.acceptable) it !in correct else it !in incorrect }
        if (trace == null && minimized) {
            break
        }
        if (trace != null) {
	    trainSet += trace
        }
        val prefixTree = buildPrefixTree(trainSet)
        prefixTree.createDotFile("init_prefix_tree")
        minimized = trace == null
        automaton = mainStrategy(
            prefixTree = prefixTree,
            timersNumber = timersNumber,
            infinity = infinity,
            solution = "automaton_rti.mzn",
            range = automaton.edgesAndStates.second.size..Int.MAX_VALUE,
            needMinimize = minimized)
            ?: throw IllegalStateException("Can't generate automaton, strange")
    }
    return automaton*/
    
    return mainStrategy(
        prefixTree = buildPrefixTree(train),
        timersNumber = timersNumber,
        infinity = infinity,
        solution = "automaton_rti.mzn",
        needMinimize = false)
        ?: throw IllegalStateException("Can't generate automaton, strange")
}

const val defaultTest = 1
const val defaultTrainCount = 20
const val defaultTestCount = 1000
const val defaultSeed = 123

const val helpTester = """Hay everyone who want to test solution!
We provide you usage of following flags:
    (-s | --source) <NUMBER> - test number you want to run. By default: $defaultTest.
    (-t | --train) <NUMBER> - training traces count. By default: $defaultTrainCount.
    (-c | --check) <NUMBER> - testing traces count. By default: $defaultTestCount.
    (-i | --infinity) <NUMBER> - infinity you want to use in automaton.
    (-sd | --seed) <NUMBER> - seed for random choosing. By default: $defaultSeed.
    (-h | --help) - program will print help message to you.
"""

data class TesterInfo(val test: Int,
                      val trainStream: InputStream,
                      val testStream: InputStream,
                      val solution: Int?,
                      val trainCount: Int,
                      val testCount: Int,
                      val infinity: Int?,
                      val seed: Int,
                      val help: String)

fun parseConsoleArgumentsTester(args: Array<String>): TesterInfo {
    val map = parseConsoleArguments(args)
    return TesterInfo(
        map.getFirstArg(listOf("-s", "--source"), defaultTest) { it[0].toInt() },
        map.getFirstArg(listOf("-s", "--source"), defaultTest) { it[0].toInt() }.let { File("$DIR/$PREFIX$it/train").inputStream() },
        map.getFirstArg(listOf("-s", "--source"), defaultTest) { it[0].toInt() }.let { File("$DIR/$PREFIX$it/test").inputStream() },
        map.getFirstArg(listOf("-sn", "--solution"), null) { it[0].toInt() },
        map.getFirstArg(listOf("-t", "--train"), defaultTrainCount) { it[0].toInt() },
        map.getFirstArg(listOf("-c", "--check"), defaultTestCount) { it[0].toInt() },
        map.getFirstArg(listOf("-i", "--infinity"), null) { it[0].toInt() },
        map.getFirstArg(listOf("-sd", "--seed"), defaultSeed) { it[0].toInt() },
        map.getFirstArg(listOf("-h", "--help"), "") { helpTester })
}

data class TimeWrapper<T>(val result: T, val time: Double)

inline fun <T> time(func: () -> T): TimeWrapper<T> {
    val startTime = System.currentTimeMillis()
    val result = func()
    val stopTime = System.currentTimeMillis()
    return TimeWrapper(result, (stopTime - startTime).toDouble() / 1000)
}

fun main(args: Array<String>) {
    val testerInfo = parseConsoleArgumentsTester(args)
    print(testerInfo.help)
    if (testerInfo.help != "") return

    val random = Random(seed = testerInfo.seed)
    val trainProgramTraces = readTraces(testerInfo.trainStream)
    val trainSet = (trainProgramTraces.validTraces + trainProgramTraces.invalidTraces).shuffled(random).take(testerInfo.trainCount)
    val testProgramTraces = readTraces(testerInfo.testStream)
    val testSet = (testProgramTraces.validTraces + testProgramTraces.invalidTraces).shuffled(random).take(testerInfo.testCount)

    val infinity = testerInfo.infinity ?: trainSet.infinity()

    val curPrefix = "$DIR/$PREFIX${testerInfo.test}"
    val directoryName = "$curPrefix/solution${ testerInfo.solution ?: takeEmpty(curPrefix,"solution") }"
    val directory = Paths.get(directoryName)
    if (Files.exists(directory)) {
        directory.toFile().deleteRecursively()
    }
    Files.createDirectory(directory)

    PrintWriter("$directoryName/info").apply {
        println("train count = ${testerInfo.trainCount}")
        println("test count = ${testerInfo.testCount}")
        println("infinity = $infinity")
        println("seed = ${testerInfo.seed}")
        flush()
    }.close()

    PrintWriter("$directoryName/info_machine").apply {
        println(testerInfo.trainCount)
        println(testerInfo.testCount)
        println(infinity)
        println(testerInfo.seed)
        flush()
    }.close()

    PrintWriter("$directoryName/result").apply {
        println("total time = -1")
        println("f-measure = -1")
        println("positive examples correctness = -1")
        println("negative examples correctness = -1")
        println("examples correctness = -1")
        flush()
    }.close()

    PrintWriter("$directoryName/result_machine").apply {
        repeat(5) { println(-1) }
        flush()
    }.close()

    val (automaton, time) = time { trainAutomaton(trainSet, timersNumber = 1, infinity = infinity) }

    val (f, ann) = automaton.checkAllTraces(trainSet)
    val s = ann.map { it.trace }
    if (f.any { !it.acceptable } || s.any { it.acceptable }) {
        throw Exception("Not all train traces is correct:\n$f\n$s")
    }

    val (correct, annotated) = automaton.checkAllTraces(testSet)
    val incorrect = annotated.map { it.trace }
    val (initCorrect, initIncorrect) = testSet.partition { it.acceptable }
    val (cor2Cor, cor2Incor) = initCorrect.partition { it in correct }
    val (incor2Incor, incor2Cor) = initIncorrect.partition { it in incorrect }

    val measure = fMeasure(
        listOf(listOf(cor2Cor.size, cor2Incor.size),
            listOf(incor2Cor.size, incor2Incor.size)))
    System.err.println("Current measure: $measure")

    automaton.createDotFile("$directoryName/solution", inf = infinity)
    PrintWriter("$directoryName/solution_machine").apply {
        println(automaton)
        flush()
    }.close()

    PrintWriter("$directoryName/result").apply {
        println("total time = $time")
        println("f-measure = $measure")
        println("positive examples correctness = ${cor2Cor.size.toDouble() / correct.size}")
        println("negative examples correctness = ${incor2Incor.size.toDouble() / incorrect.size}")
        println("examples correctness = ${(cor2Cor.size + incor2Incor.size).toDouble() / (correct.size + incorrect.size)}")
        flush()
    }.close()

    PrintWriter("$directoryName/result_machine").apply {
        println(time)
        println(measure)
        println(cor2Cor.size.toDouble() / correct.size)
        println(incor2Incor.size.toDouble() / incorrect.size)
        println((cor2Cor.size + incor2Incor.size).toDouble() / (correct.size + incorrect.size))
        flush()
    }.close()
}
