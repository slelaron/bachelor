import java.io.File
import java.io.InputStream
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Paths
import kotlin.random.Random

data class Environment(
    val solution: String = "automaton_cbs.mzn",
    val solver: String = "org.chuffed.chuffed",
    val traces: List<Trace>,
    val statesNumber: Int = 0,
    val vertexDegree: Int = statesNumber * traces.labels().size,
    val maxTotalEdges: Int = vertexDegree * statesNumber,
    val timersNumber: Int,
    val infinity: Int,
    val samplingDegree: Int? = null,
    val maxActiveTimersCount: Int = maxTotalEdges * timersNumber
) {
    override fun toString() =
            "{ solution: $solution, solver: $solver, states: $statesNumber, samplingDegree: $samplingDegree, " +
                    "infinity: $infinity, vertex degree: $vertexDegree, edges: $maxTotalEdges, " +
                    "timers: $timersNumber, active timers: $maxActiveTimersCount }"

    val prefixTree: Tree?
        get() = try {
            buildPrefixTree(traces.sample())
        } catch (ex: Exception) {
            null
        }

    fun Iterable<Trace>.sample() = if (samplingDegree != null) traces.map { it.sample(samplingDegree, infinity) } else traces
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
        val vertexDegree = statesNumber * (env.prefixTree?.labels()?.size ?: 0)
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

class CGAR(val list: MutableList<Trace>,
           private val train: Iterable<Trace>,
           val restore: (Environment) -> Environment,
           var nxt: Strategy? = null,
           var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        if (prev == null) throw Exception("null prev")

        //prev.createDotFile("debug")	
        val verdict = prev.checkAllTraces(train, env.samplingDegree, env.infinity)
        val correct = verdict.correct.toSet()
        val incorrect = verdict.incorrect.map { it.trace }.toSet()
        //System.err.println("Correct:\n${correct.joinToString("\n")}\n")
        //System.err.println("Incorrect:\n${verdict.incorrect.joinToString("\n") { "${it.trace} | ${it.reason}" }}\n")
        val trace = train.sortedBy { it.records.size }.firstOrNull { if (it.acceptable) it !in correct else it !in incorrect }
        //System.err.println("Added: $trace")
        return when (trace) {
            null -> StrategyStep(env, null, nxt)
            else -> {
                //System.err.println(trace)
                list += trace
                val prefixTree = buildPrefixTree(with(env) { list.sample() })
                prefixTree.createDotFile("init_prefix_tree")
                System.err.println("Prefix tree traces number: ${list.size}")
                StrategyStep(restore(env).copy(traces = list.toList()), null, nxt2)
            }
        }
    }
}

fun strategyBuilder(train: Iterable<Trace>,
                    list: MutableList<Trace>): Strategy {
    val decVertexDegree = DecVertexDegree()
    val decEdges = DecEdges()
    val incStates = IncStates()
    val decActiveTimers = DecActiveTimers()
    val cgar1 = CGAR(list, train, {
        val vertexDegree = it.vertexDegree + 1
        val maxTotalEdges = vertexDegree * it.statesNumber
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar2 = CGAR(list, train, {
        val maxTotalEdges = it.maxTotalEdges + 1
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar3 = CGAR(list, train, {
        it.copy(maxActiveTimersCount = it.maxActiveTimersCount + 1)
    })
    val cgar0 = CGAR(list, train, {
        val statesNumber = it.statesNumber - 1
        val vertexDegree = statesNumber * (it.prefixTree?.labels()?.size ?: 0)
        val maxTotalEdges = vertexDegree * statesNumber
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

class IncStatesAndSampling(var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val index = order.withIndex().find { env.statesNumber to (env.samplingDegree ?: 1) == it.value }?.index
            ?: throw Exception("No such pair in order: (${env.statesNumber} ${env.samplingDegree ?: 1}")
        val statesNumber = order[index + 1].first
        val samplingDegree = order[index + 1].second
        val vertexDegree = samplingDegree * (env.prefixTree?.labels()?.size ?: 0)
        val maxTotalEdges = vertexDegree * statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        val environment = env.copy(
            statesNumber = statesNumber,
            samplingDegree = samplingDegree,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(environment, prev, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }

    companion object {
        val order = (List(100) { states ->
            List(100) { (states + 1) to (it + 1) }
        }.flatten() + (0 to 1)).sortedBy { it.first * it.second }
    }
}

data class Counter(var now: Int = 0)

class IncStatesAndDegree(val counter: Counter, var nxt: Strategy? = null, var nxt2: Strategy? = null): Strategy {
    override fun next(env: Environment, prev: Automaton?): StrategyStep {
        val index = ++counter.now
        val statesNumber = order[index].first
        val vertexDegree = order[index].second
        val maxTotalEdges = vertexDegree * statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        val environment = env.copy(
            statesNumber = statesNumber,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
        //System.err.println("New environment: $environment")
        return when (val automaton = environment.generateAutomaton()) {
            null -> StrategyStep(environment, prev, nxt)
            else -> StrategyStep(update(environment, automaton), automaton, nxt2)
        }
    }

    companion object {
        val order = (List(100) { states ->
            List(100) { (states + 1) to (it + 1) }
        }.flatten() + (0 to 0)).sortedBy {
            1000 * it.first * it.second + 2 * maxOf(it.first, it.second) + if (it.first > it.second) 0 else 1
        }
    }
}

fun strategyBuilderNew(train: Iterable<Trace>,
                       list: MutableList<Trace>): Strategy {
    val decVertexDegree = DecVertexDegree()
    val decEdges = DecEdges()
    val incStatesAndSampling = IncStatesAndSampling()
    val decActiveTimers = DecActiveTimers()
    val cgar0 = CGAR(list, train, { env ->
        val index = IncStatesAndSampling.
            order.withIndex().find { env.statesNumber to env.samplingDegree == it.value }?.index
            ?: throw Exception("No such pair in order")
        val statesNumber = IncStatesAndSampling.order[index - 1].first
        val samplingDegree = IncStatesAndSampling.order[index - 1].second
        val vertexDegree = samplingDegree * (env.prefixTree?.labels()?.size ?: 0)
        val maxTotalEdges = vertexDegree * statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        env.copy(
            statesNumber = statesNumber,
            samplingDegree = samplingDegree,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar1 = CGAR(list, train, {
        val vertexDegree = it.vertexDegree + 1
        val maxTotalEdges = vertexDegree * it.statesNumber
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar2 = CGAR(list, train, {
        val maxTotalEdges = it.maxTotalEdges + 1
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar3 = CGAR(list, train, {
        it.copy(maxActiveTimersCount = it.maxActiveTimersCount + 1)
    })
    incStatesAndSampling.apply {
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
        nxt2 = incStatesAndSampling
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
    return incStatesAndSampling
}

fun strategyBuilderNew2(train: Iterable<Trace>,
                       list: MutableList<Trace>): Strategy {
    val decEdges = DecEdges()
    val counter = Counter()
    val incStatesAndDegree = IncStatesAndDegree(counter)
    val decActiveTimers = DecActiveTimers()
    val cgar0 = CGAR(list, train, { env ->
        val index = --counter.now
        val statesNumber = IncStatesAndDegree.order[index].first
        val vertexDegree = IncStatesAndDegree.order[index].second
        val maxTotalEdges = vertexDegree * statesNumber
        val maxActiveTimersCount = maxTotalEdges * env.timersNumber
        env.copy(
            statesNumber = statesNumber,
            vertexDegree = vertexDegree,
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar2 = CGAR(list, train, {
        val maxTotalEdges = it.maxTotalEdges + 1
        val maxActiveTimersCount = maxTotalEdges * it.timersNumber
        it.copy(
            maxTotalEdges = maxTotalEdges,
            maxActiveTimersCount = maxActiveTimersCount)
    })
    val cgar3 = CGAR(list, train, {
        it.copy(maxActiveTimersCount = it.maxActiveTimersCount + 1)
    })
    incStatesAndDegree.apply {
        nxt = this
        nxt2 = cgar0
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
        nxt = decEdges
        nxt2 = incStatesAndDegree
    }
    cgar2.apply {
        nxt = decEdges
        nxt2 = decEdges
    }
    cgar3.apply {
        nxt = decActiveTimers
        nxt2 = decActiveTimers
    }
    return incStatesAndDegree
}

fun Trace.sample(degree: Int, inf: Int) = Trace(run {
    val infinity = inf.toLong() + 1
    val degrees = List(degree) {
        (infinity * it / degree).toInt()..((infinity * (it + 1) / degree) - 1).toInt()
    }
    records.map { (name, time) ->
        Record(name, degrees.withIndex().find { time in it.value }?.index
            ?: throw Exception("Wrong time=$time value with infinity=$inf. List: $degrees"))
    }
}, acceptable)

fun runStrategies(train: Iterable<Trace>,
                  timersNumber: Int,
                  infinity: Int?,
                  checker: Environment?.(Automaton) -> Unit): Automaton {
    val list = mutableListOf(train.sortedBy { it.records.size }.first())
    var env = Environment(
        solution = "automaton_rti.mzn",
        /*samplingDegree = 1,*/
        traces = list,
        timersNumber = timersNumber,
        infinity = infinity ?: /*train.infinity()*/ (train.mapNotNull { t ->  t.records.map { it.time }.max() }.max() ?: 0))
    var now: Strategy? = strategyBuilderNew2(train, list)
    var automaton: Automaton? = null
    var counter = 0
    while (now != null) {
        val next  = now.next(env, automaton)
        env = next.environment
        now = next.strategy
        if (next.automaton != null) {
            automaton = next.automaton
            val (f, ann) = automaton.checkAllTraces(train, env.samplingDegree, env.infinity)
            val s = ann.map { it.trace }
            if (f.all { it.acceptable } && s.all { !it.acceptable }) {
                env.checker(automaton)
            }
        }
    }
    return automaton ?: throw Exception("No automaton")
}

fun mainStrategy(traces: List<Trace>,
                 timersNumber: Int,
                 range: IntRange = 1..Int.MAX_VALUE,
                 solution: String = "automaton_cbs.mzn",
                 solver: String  = "org.chuffed.chuffed",
                 vertexDegree: Int? = null,
                 maxTotalEdges: Int? = null,
                 maxActiveTimersCount: Int? = null,
                 infinity: Int = traces.infinity(),
                 needMinimize: Boolean = false): Automaton? {
    val labels = traces.labels().count()
    var automaton: Automaton?
    for (statesNumber in range) {
        val theVertexDegree = vertexDegree ?: statesNumber * labels
        val theMaxTotalEdges = maxTotalEdges ?: (theVertexDegree * statesNumber)
        val theMaxActiveTimersCount = maxActiveTimersCount ?: (theMaxTotalEdges * timersNumber)
        val environment = Environment(
            solution,
            solver,
            traces,
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
            traces = trainSet.toList(),
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
                      val algorithm: (Iterable<Trace>, Int, Int, Environment?.(Automaton) -> Unit) -> Automaton,
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
            { train: Iterable<Trace>, _: Int, infinity: Int, func: Environment?.(Automaton) -> Unit ->
                rti(train, infinity).also { null.func(it) } as Automaton
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
            val train = if (this != null) trainSet.sample() else trainSet
            val (measure, posPercentage, negPercentage, percentage) = estimate(automaton, train, testSet)
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
