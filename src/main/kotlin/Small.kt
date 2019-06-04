data class Test(val number: Int, val states: Int, val labels: Int, val splits: Int, val inf: Int): Comparable<Test> {
    override fun compareTo(other: Test) =
        compareValuesBy(this, other, { it.states * it.labels + it.splits }, { it.states }, { it.labels }, { it.splits }, { it.inf }, { it.number })
}

fun main() {
    val tests = mutableListOf<Test>()
    var number = 1
    for (states in 2..8) {
        for (labels in 2..4) {
            for (splits in listOf(2, 4, 8)) {
                for (inf in listOf(10, 20)) {
                    tests += Test(number++, states, labels, splits, inf)
                }
            }
        }
    }
    tests.sort()
    println(tests.joinToString(" ") { "${it.number}" })
}