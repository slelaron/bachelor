import java.nio.file.Files
import java.nio.file.Paths

fun main(args: Array<String>) {
    val map = parseConsoleArguments(args)
    val mn = map.getFirstArg(listOf("-mn"), 1) { it[0].toInt() }
    val order = getOrder()
    val mx = map.getFirstArg(listOf("-mx"), 20) { it[0].toInt() }
    val index = map.getFirstArg(listOf("-id"), 0) { it[0].toInt() }
    val testNumber = map.getFirstArg(listOf("-t", "--test"), 3393) { it[0].toInt() }

    for (test in order.take(testNumber)) {
        for (solution in mn..mx) {
	    val curPrefix = "$DIR/$PREFIX${test.number}"
	    val directoryName = "$curPrefix/solution${solution + 1999}"
	    val directory = Paths.get(directoryName)
	    if (Files.exists(directory)) {
                continue
	    }
            System.err.println("Start: Test: ${test.number}, solution: $solution")
            val testerInfo = TesterInfo(
                test = test.number,
                solution = solution + 1999,
                trainCount = 20,
                infinity = test.inf,
                seed = solution,
                index = index,
                algorithm = usualAlgorithm()
            )
            testIt(testerInfo)
            System.err.println("End: Test: ${test.number}, solution: $solution")
        }
    }
}
