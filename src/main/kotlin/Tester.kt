import jdk.jfr.Percentage
import java.io.File
import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Paths
import kotlin.random.Random

data class Environment(
    val solution: String = "automaton_cbs.mzn",
    val solver: String = "org.chuffed.chuffed",
    val prefixTree: Tree,
    val statesNumber: Int = 0,
    val vertexDegree: Int = statesNumber * prefixTree.labels().size,
    val maxTotalEdges: Int = vertexDegree * statesNumber,
    val timersNumber: Int,
    val infinity: Int,
    val maxActiveTimersCount: Int = maxTotalEdges * timersNumber
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

data class StrategyStep(val environment: Environment, val automaton: Automaton?, val strategy: Strategy?)

fun update(env: Environment, automaton: Automaton): Environment {
    val (edges, states) = automaton.edgesAndStates
    return env.copy(
        statesNumber = states.size,
        vertexDegree = automaton.vertexDegree(),
        maxTotalEdges = edges.size,
        maxActiveTimersCount = automaton.edgesAndStates.first.sumBy { e -> e.conditions.timeGuards.size }
        )
}

interface Strategy {
    fun next(env: Environment, prev: Automaton?): StrategyStep
}

class DecActiveTimers(var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val environment = env.copy(
            maxActiveTimersCount = env.maxActiveTimersCount - 1)
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(env, null, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }

}

class DecEdges(var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val maxTotalEdges = env.maxTotalEdges - 1
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        val environment = env.copy(
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(env, null, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }

}

class DecVertexDegree(var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val vertexDegree = env.vertexDegree - 1
        val maxTotalEdges = vertexDegree * env.statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        val environment = env.copy(
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(env, null, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }

}

class IncStates(var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val statesNumber = env.statesNumber + 1
        val vertexDegree = statesNumber * env.prefixTree.labels().size
        val maxTotalEdges = vertexDegree * statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        val environment = env.copy(
            statesNumber = statesNumber,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(environment, prev, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }
}

class CGAR(val set: MutableSet<Trace>,
           private val train: Iterable<Trace>,
           val restore: (Environment) -> Environment,
           var nxt: Strategy? = null,
           var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        if (prev == null) throw Exception("null prev")

        val verdict = prev.checkAllTraces(train)
        val correct = verdict.correct.toSet()
        val incorrect = verdict.incorrect.map { it.trace }.toSet()
        val trace = train.sortedBy { it.records.size }.firstOrNull { if (it.acceptable) it !in correct else it !in incorrect }
        return when (trace) {
            null -> StrategyStep(env, null, nxt)
            else -> {
                set += trace
                val prefixTree = buildPrefixTree(set)
                prefixTree.createDotFile("init_prefix_tree")
                System.err.println("Prefix tree traces number: ${set.size}")
                StrategyStep(restore(env).copy(prefixTree = prefixTree), null, nxt2)
            }
        }
    }
}

fun strategyBuilder(train: Iterable<Trace>,
                    set: MutableSet<Trace>): Strategy {
    val decVertexDegree = DecVertexDegree()
    val decEdges = DecEdges()
    val incStates = IncStates()
    val decActiveTimers = DecActiveTimers()
    val cgar1 = CGAR(set, train, {
        val vertexDegree = it.vertexDegree + 1
        val maxTotalEdges = vertexDegree * it.statesNumber
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar2 = CGAR(set, train, {
        val maxTotalEdges = it.maxTotalEdges + 1
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar3 = CGAR(set, train, {
        it.copy(maxActiveTimersCount = it.maxActiveTimersCount + 1)
    })
    val cgar0 = CGAR(set, train, { 
        val statesNumber = it.statesNumber - 1
        val vertexDegree = statesNumber * it.prefixTree.labels().size
        val maxTotalEdges = vertexDegree * it.statesNumber
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            statesNumber = statesNumber,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    incStates.apply {
        nxt = this
        nxt2 = cgar0
    }
    decVertexDegree.apply {
        nxt = decEdges
        nxt2 = cgar1
    }
    decEdges.apply {
        nxt = decActiveTimers
        nxt2 = cgar2
    }
    decActiveTimers.apply {
        nxt = null
        nxt2 = cgar3
    }
    cgar0.apply {
        nxt = decVertexDegree
        nxt2 = incStates
    }
    cgar1.apply {
        nxt = decVertexDegree
        nxt2 = decVertexDegree
    }
    cgar2.apply {
        nxt = decEdges
        nxt2 = decEdges
    }
    cgar3.apply {
        nxt = decActiveTimers
        nxt2 = decActiveTimers
    }
    return incStates
}

fun runStrategies(train: Iterable<Trace>,
                  timersNumber: Int,
                  infinity: Int?,
                  checker: (Automaton) -> Unit): Automaton {
    val set = mutableSetOf(train.sortedBy { it.records.size }.first())
    var env = Environment(
        solution = "automaton_rti.mzn",
        prefixTree = buildPrefixTree(set),
        timersNumber = timersNumber,
        infinity = infinity ?: train.infinity())
    var now: Strategy? = strategyBuilder(train, set)
    var automaton: Automaton? = null
    var counter = 0
    while (now != null) {
        val next  = now.next(env, automaton)
        env = next.environment
        now = next.strategy
        if (next.automaton != null) {
            automaton = next.automaton
            val (f, ann) = automaton.checkAllTraces(train)
            val s = ann.map { it.trace }
            if (f.all { it.acceptable } && s.all { !it.acceptable }) {
                checker(automaton)
            }
        }
    }
    return automaton ?: throw Exception("No automaton")
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
                val e0 = environment.copy(vertexDegree = automaton.vertexDegree())
                val (env0, aut0) = decrease(e0, automaton, { this.vertexDegree > 1 }) {
                    copy(vertexDegree = it.vertexDegree() - 1)
                }
                val e1 = env0.copy(maxTotalEdges = aut0.edgesAndStates.first.size)
                val (env1, aut1) = decrease(e1, aut0, { this.maxTotalEdges > 1 }) {
                    val (edges, _) = it.edgesAndStates
                    copy(maxTotalEdges = edges.size - 1)
                }
                val e2 = env1.copy(maxActiveTimersCount = aut1.edgesAndStates.first.sumBy { e -> e.conditions.timeGuards.size })
                val (_, aut2) = decrease(e2, aut1, { this.maxActiveTimersCount > 1 }) {
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
                   infinity: Int = train.infinity(),
                   degree: Int? = null): Automaton {
    val trainSet = mutableSetOf<Trace>()
    var automaton: Automaton = MutableAutomaton(name = "q0")
    var minimized = false
    while (true) {
        val verdict = automaton.checkAllTraces(train)
        val correct = verdict.correct.toSet()
        val incorrect = verdict.incorrect.map { it.trace }.toSet()
        val trace = train.sortedBy { it.records.size }.firstOrNull { if (it.acceptable) it !in correct else it !in incorrect }
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
    return automaton
    
    /*return mainStrategy(
        prefixTree = buildPrefixTree(train),
        timersNumber = timersNumber,
        infinity = infinity,
        solution = "automaton_rti.mzn",
        needMinimize = false,
        vertexDegree = degree)
        ?: throw IllegalStateException("Can't generate automaton, strange")*/
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
    (-sn | --solution) <NUMBER> - number of solution you want to generate/regenerate.
    (-sd | --seed) <NUMBER> - seed for random choosing. By default: $defaultSeed.
    (-v | --verwer) - if you want to use rti as solution.
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
                      val realTrain: Boolean,
                      val realTest: Boolean,
                      val algorithm: (Iterable<Trace>, Int, Int, (Automaton) -> Unit) -> Automaton,
                      val postfix: String,
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
        map.getFirstArg(listOf("-rt", "--realTrain"), false) { true },
        map.getFirstArg(listOf("-rc", "--realCheck"), false) { true },
        map.getFirstArg(listOf("-v", "--verwer"), { train, timersNumber, infinity, func ->
            runStrategies(train, timersNumber, infinity, func) }
        ) {
            { train: Iterable<Trace>, _: Int, infinity: Int, func: (Automaton) -> Unit ->
                rti(train, infinity).also { func(it) } as Automaton
            }
        },
        map.getFirstArg(listOf("-v", "--verwer"), "") { "_verwer" },
        map.getFirstArg(listOf("-h", "--help"), "") { helpTester })
}

interface TimeEvaluator {
    val time: Double
}

inline fun <T> time(func: TimeEvaluator.() -> T): T {
    val startTime = System.currentTimeMillis()
    return object: TimeEvaluator {
        override val time
            get() = (System.currentTimeMillis() - startTime).toDouble() / 1000
    }.func()
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

    PrintWriter("$directoryName/info${testerInfo.postfix}").apply {
        println("train count = ${testerInfo.trainCount}")
        println("test count = ${testerInfo.testCount}")
        println("infinity = $infinity")
        println("seed = ${testerInfo.seed}")
        flush()
    }.close()

    PrintWriter("$directoryName/info_machine${testerInfo.postfix}").apply {
        println(testerInfo.trainCount)
        println(testerInfo.testCount)
        println(infinity)
        println(testerInfo.seed)
        flush()
    }.close()

    PrintWriter("$directoryName/result${testerInfo.postfix}").apply {
        println("total time = -1")
        println("f-measure = -1")
        println("positive examples correctness = -1")
        println("negative examples correctness = -1")
        println("examples correctness = -1")
        flush()
    }.close()

    PrintWriter("$directoryName/result_machine${testerInfo.postfix}").apply {
        repeat(5) { println(-1) }
        flush()
    }.close()

    /*for (train in trainSet) {
        System.err.println(train)
    }*/

    //val correctAutomaton = readAutomaton(Scanner(File("$DIR/$PREFIX${testerInfo.test}/automaton")))

    time {
        //val automaton = trainAutomaton(trainSet, timersNumber = 1, infinity = infinity)
        //val automaton = rti(trainSet, infinity)
        //runStrategies(trainSet, timersNumber = 1, infinity = infinity) { automaton ->
        testerInfo.algorithm(trainSet, 1, infinity) { automaton ->
            val (measure, posPercentage, negPercentage, percentage) = estimate(automaton, trainSet, testSet)
            System.err.println("Current measure: $measure")

            if (testerInfo.postfix != "_verwer") {
                automaton.createDotFile("$directoryName/solution${testerInfo.postfix}", inf = infinity)
            }
            PrintWriter("$directoryName/solution_machine${testerInfo.postfix}").apply {
                println(automaton)
                flush()
            }.close()

            PrintWriter("$directoryName/result${testerInfo.postfix}").apply {
                println("total time = $time")
                println("f-measure = $measure")
                println("positive examples correctness = $posPercentage")
                println("negative examples correctness = $negPercentage")
                println("examples correctness = $percentage")
                flush()
            }.close()

            PrintWriter("$directoryName/result_machine${testerInfo.postfix}").apply {
                println(time)
                println(measure)
                println(posPercentage)
                println(negPercentage)
                println(percentage)
                flush()
            }.close()
        }
    }
}
