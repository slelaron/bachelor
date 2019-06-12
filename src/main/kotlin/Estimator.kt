import java.io.File
import java.util.*

data class TestInfo(val measure: Double, val posPercentage: Double, val negPercentage: Double, val percentage: Double)

fun estimate(automaton: Automaton, trainSet: Iterable<Trace>, testSet: Iterable<Trace>): TestInfo {
    val (f, ann) = automaton.checkAllTraces(trainSet)
    val s = ann.map { it.trace }
    if (f.any { !it.acceptable } || s.any { it.acceptable }) {
        throw Exception("Not all train traces is correct:\n${
            (f.filter { !it.acceptable } + s.filter { it.acceptable }).joinToString("\n")
        }")
    }

    val (correct, annotated) = automaton.checkAllTraces(testSet)
    val incorrect = annotated.map { it.trace }
    val (initCorrect, initIncorrect) = testSet.partition { it.acceptable }
    val (cor2Cor, cor2Incor) = initCorrect.partition { it in correct }
    val (incor2Incor, incor2Cor) = initIncorrect.partition { it in incorrect }

    val measure = fMeasure(
        listOf(
            listOf(cor2Cor.size, cor2Incor.size),
            listOf(incor2Cor.size, incor2Incor.size)
        )
    )

    return TestInfo(measure,
        cor2Cor.size.toDouble() / correct.size,
        incor2Incor.size.toDouble() / incorrect.size,
        (cor2Cor.size + incor2Incor.size).toDouble() / (correct.size + incorrect.size))
}

fun main(args: Array<String>) {
    val map = parseConsoleArguments(args)
    val aut = map.getFirstArg(listOf("-s", "--source"), System.`in`) { File(it[0]).inputStream() }
    val train = map.getFirstArg(listOf("-t", "--train"), System.`in`) { File(it[0]).inputStream() }
    val test = map.getFirstArg(listOf("-c", "--check"), System.`in`) { File(it[0]).inputStream() }

    val automaton = readAutomaton(Scanner(aut))
    val trainSet = readTraces(train)
    val testSet = readTraces(test)

    val (measure, posPercentage, negPercentage, percentage) =
        estimate(automaton,
            (trainSet.validTraces + trainSet.invalidTraces).filterNot { it.records.isEmpty() },
            (testSet.validTraces + testSet.invalidTraces).filterNot { it.records.isEmpty() })

    println("f-measure = $measure")
    println("positive examples correctness = $posPercentage")
    println("negative examples correctness = $negPercentage")
    println("examples correctness = $percentage")
}
