import kotlin.random.Random

interface AutomatonGenerator: Iterable<Automaton> {
    class EdgeBuilder(var from: MutableAutomaton,
                      var to: MutableAutomaton,
                      var label: String,
                      val guards: Map<Timer, IntRange> = mutableMapOf(),
                      val resets: MutableSet<Timer> = mutableSetOf(),
                      val splitAt: MutableSet<Int> = mutableSetOf())
}

class AutomatonGeneratorOneTimer(val statesNumber: Int,
                                 val splitsNumber: Int,
                                 val timeUpperBound: Int,
                                 val labels: List<String>,
                                 val resetProbability: Double = 0.0): AutomatonGenerator {
    override fun iterator() = object: Iterator<Automaton> {
        override fun next(): Automaton {
            val timer = 0
            val garbage = MutableAutomaton(name = "q$statesNumber")
            val states = List(statesNumber) { MutableAutomaton(name = "q$it") }
            val possibleEdges = states.flatMap { i ->
                labels.map { AutomatonGenerator.EdgeBuilder(i, garbage, it) }
            }
            for (i in 0 until splitsNumber) {
                val edge = possibleEdges.random()
                val time = (0 until timeUpperBound).random()
                edge.splitAt += time
            }
            val dividedEdges = possibleEdges.flatMap { edge ->
                listOf(*edge.splitAt.toTypedArray(), Int.MAX_VALUE, 0).sorted().zipWithNext { a, b ->
                    AutomatonGenerator.EdgeBuilder(edge.from, edge.to, edge.label, mutableMapOf(timer to (a until b)))
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
            for (state in states) {
                state.final = Random.nextBoolean()
            }
            return states[0]
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
                    when (val result = state.nextState(now.name, timerManager)) {
                        is ErrorContainer -> throw IllegalStateException(result.error)
                        is AnswerContainer -> result.answer
                    }
                for (timer in resets) {
                    timerManager.reset(timer)
                }
                state = next
                records += now
            }
            return Trace(records, Random.nextBoolean())
        }
    }
}

fun fMeasure(answers: List<List<Int>>): Double {
    if (answers.any { a -> answers.firstOrNull()?.let { it.size != a.size } == true })
        throw IllegalStateException("Wrong passed matrix")
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

data class TestData(val generator: AutomatonGenerator,
                    val timeUpperBound: Int,
                    val stopProbability: Double,
                    val labels: List<String>,
                    val vertexDegree: Int,
                    val timersNumber: Int,
                    val trainTraceCount: Int,
                    val testTraceCount: Int)

fun trainAutomaton(train: List<Trace>,
                   vertexDegree: Int,
                   timersNumber: Int,
                   maxTotalEdges: Int = 0,
                   infinity: Int = train.infinity()): Automaton {
    val trainSet = mutableSetOf<Trace>()
    var automaton: Automaton = MutableAutomaton(name = "q0")
    while (true) {
        val verdict = automaton.checkAllTraces(train)
        val correct = verdict.correct.toSet()
        val incorrect = verdict.incorrect.map { it.trace }.toSet()
        val trace = train.firstOrNull { if (it.acceptable) it !in correct else it !in incorrect } ?: break
        trainSet += trace
        val prefixTree = buildPrefixTree(trainSet)
        prefixTree.createDotFile("init_prefix_tree")
        automaton = generateAutomaton(
            prefixTree,
            vertexDegree,
            timersNumber,
            maxTotalEdges,
            infinity,
            automaton.edgesAndStates.first.size..Int.MAX_VALUE)
            ?: throw IllegalStateException("Can't generate automaton, strange")
    }
    val verdict = automaton.checkAllTraces(train)
    if (verdict.incorrect.isNotEmpty())
        throw IllegalStateException("Not all traces are ")
    return automaton
}

fun test(testData: List<TestData>) {
    for ((
        generator,
        timeUpperBound,
        stopProbability,
        labels,
        vertexDegree,
        timersNumber,
        trainTraceCount,
        testTraceCount) in testData) {
        for (init in generator.take(1)) {
            init.createDotFile("init_test")
            System.err.println("Start testing")
            val pathGenerator = PathGenerator(init, timeUpperBound, stopProbability, labels)
            val trainSet = pathGenerator.take(trainTraceCount)
            val testSet = pathGenerator.take(testTraceCount)
            val automaton = trainAutomaton(trainSet, vertexDegree, timersNumber)
            val (correct, annotated) = automaton.checkAllTraces(testSet)
            val incorrect = annotated.map { it.trace }
            val (initCorrect, initIncorrect) = testSet.partition { it.acceptable }
            val (cor2Cor, cor2Incor) = initCorrect.partition { it in correct }
            val (incor2Incor, incor2Cor) = initIncorrect.partition { it in incorrect }
            val measure = fMeasure(listOf(listOf(cor2Cor.size, cor2Incor.size), listOf(incor2Cor.size, incor2Incor.size)))
            System.err.println("Current measure: $measure")
        }
    }
}

fun main() {
    val splitsNumber = 16
    val statesNumber = 16
    val timerNumber = 1
    val trainTraceCount = 1000
    val testTraceCount = 1000
    val labels = listOf("a", "b", "c", "d")
    val resetProbability = 1.0
    val timeUpperBound = 100
    val stopProbability = 0.1

    val generator = AutomatonGeneratorOneTimer(
        statesNumber,
        splitsNumber,
        timeUpperBound,
        labels,
        resetProbability
    )
    test(listOf(TestData(
        generator,
        timeUpperBound,
        stopProbability,
        labels,
        labels.size * (splitsNumber + 1),
        timerNumber,
        trainTraceCount,
        testTraceCount)))
}
