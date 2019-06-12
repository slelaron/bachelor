data class Test(val number: Int, val states: Int, val labels: Int, val splits: Int, val inf: Int): Comparable<Test> {
    override fun compareTo(other: Test) =
        compareValuesBy(this, other, { it.states * it.labels + it.splits }, { it.states }, { it.labels }, { it.splits }, { it.inf }, { it.number })
}

fun getOrder(): List<Test> {
    val tests = mutableListOf<Test>()
    var number = 1000
    for (states in 2..8) {
        for (labels in 2..4) {
            for (splits in listOf(2, 4, 8)) {
                for (inf in listOf(10, 20)) {
                    for (num in 1..19) {
                        tests += Test(number, states, labels, splits, inf)
                        number++
                    }
                }
            }
        }
    }
    tests.sort()
    return tests
}

fun main(args: Array<String>) {
    val map = parseConsoleArguments(args)
    val number = map.getFirstArg(listOf("-nm", "--number"), null) { it[0].toInt() }
    if (number != null) {
        val result = getOrder().withIndex().firstOrNull { it.value.number == number }
        if (result == null) {
            println("Not found")
        } else {
            println("${result.index}")
        }
    } else {
        println(getOrder().joinToString(" ") { "${it.number}" })
    }
}
