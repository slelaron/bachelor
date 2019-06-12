import java.io.File
import java.io.InputStream
import java.io.PrintWriter
import kotlin.random.Random

data class VerwerData(val source: Int,
                      val trainStream: InputStream,
                      val testStream: InputStream)

fun parseConsoleArgumentsVerwer(args: Array<String>): VerwerData {
    val map = parseConsoleArguments(args)
    return VerwerData(
        map.getFirstArg(listOf("-s", "--source"), 1) { it[0].toInt() },
        map.getFirstArg(listOf("-s", "--source"), 1) { it[0].toInt() }.let { File("$DIR/$PREFIX$it/train").inputStream() },
        map.getFirstArg(listOf("-s", "--source"), 1) { it[0].toInt() }.let { File("$DIR/$PREFIX$it/test").inputStream() })
}

fun main(args: Array<String>) {
    val parsed = parseConsoleArgumentsVerwer(args)

    val random = Random(seed = defaultSeed)
    val testProgramTraces = readTraces(parsed.testStream)
    val testSet = (testProgramTraces.validTraces + testProgramTraces.invalidTraces).shuffled(random).filterNot { it.records.isEmpty() }

    val curPrefix = "$DIR/$PREFIX${parsed.source}/verwer"
    val file = File(curPrefix)
    file.mkdirs()
    val testTraces = ProgramTraces(testSet.filter { it.acceptable }, testSet.filter { !it.acceptable })
    PrintWriter("$curPrefix/real_test_verwer").apply {
        println(testTraces.toVerwer())
        flush()
    }.close()

    val trainProgramTraces = readTraces(parsed.trainStream)
    for (take in listOf(20, 30, 40)) {
        val trainSet =
            (trainProgramTraces.validTraces + trainProgramTraces.invalidTraces).shuffled(random).take(take).filterNot { it.records.isEmpty() }
        val trainTraces = ProgramTraces(trainSet.filter { it.acceptable }, trainSet.filter { !it.acceptable })
        PrintWriter("$curPrefix/real_train_$take").apply {
            println(trainTraces)
            flush()
        }.close()
        PrintWriter("$curPrefix/real_train_verwer_$take").apply {
            println(trainTraces.toVerwer())
            flush()
        }.close()
    }
    val trainSet =
        (trainProgramTraces.validTraces + trainProgramTraces.invalidTraces).shuffled(random).filterNot { it.records.isEmpty() }
    val trainTraces = ProgramTraces(trainSet.filter { it.acceptable }, trainSet.filter { !it.acceptable })
    PrintWriter("$curPrefix/real_train").apply {
        println(trainTraces)
        flush()
    }.close()
    PrintWriter("$curPrefix/real_train_verwer").apply {
        println(trainTraces.toVerwer())
        flush()
    }.close()
}
