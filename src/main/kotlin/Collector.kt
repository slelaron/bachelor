import java.util.*
import java.io.*
import kotlin.math.roundToInt

data class Q(           val testIndex: Int,
			val solutionIndex: Int,
			val states: Int,
			val symbols: Int,
			val splits: Int,
			val inf: Int,
			val edges: Int,
			val timeGet: Double?,
			val statesGet: Int?, val edgesGet: Int?,
			val percentGet: Double?,
			val fGet: Double?)

data class R(val states: Int, val symbols: Int, val splits: Int, val edges: Int, val inf: Int): Comparable<R> {
	override fun compareTo(other: R) =
		compareValuesBy(this, other, { it.edges }, { it.states }, { it.splits }, { it.symbols }, { it.inf})
}

data class E(val time: Double, val states: Double, val edges: Double, val percent: Double, val f: Double, val noSol: Double, val fMax: Double)

data class T(val item20: E, val item30: E, val itemRTI: E, val itemRTI30: E)

fun Double.p(digits: Int) = String.format("%.${digits}f", this)
fun Double.mul() = this * 100

fun stringify(r: R, s: T) = listOf(r.edges, r.states, r.symbols, r.splits, r.inf, 
					s.item20.percent.p(1), s.item30.percent.p(1), s.itemRTI.percent.p(1), s.itemRTI30.percent.p(1),
					s.item20.f.p(2), s.item30.f.p(2), s.itemRTI.f.p(2), s.itemRTI30.f.p(2),
					s.item20.fMax.p(2), s.item30.fMax.p(2), s.itemRTI30.fMax.p(2)).joinToString(" & ", postfix = """ \\\hline""")

fun stringify1(r: R, s: T) = listOf(r.edges, r.states, r.symbols, r.splits, r.inf, 
					s.item20.noSol.p(1), s.item30.noSol.p(1), 
					s.item20.time.p(1), s.item30.time.p(1), s.itemRTI.time.p(1), s.itemRTI30.time.p(1),
					s.item20.states.p(1), s.item30.states.p(1), s.itemRTI.states.p(1), s.itemRTI30.states.p(1),
					s.item20.edges.p(2), s.item30.edges.p(2), s.itemRTI.edges.p(2), s.itemRTI30.edges.p(2)).joinToString(" & ", postfix = """ \\\hline""")

fun q(a: Double): Double? {
	if (a < 0) return null
	return a
}

const val total = 19
const val totalSolutions = 20

fun process(list: List<Q>): E {
	val ns = list.count { it.statesGet == null }
	val states = list.mapNotNull { it.statesGet }.sum().toDouble() / (list.size - ns)
	val edges = list.mapNotNull { it.edgesGet }.sum().toDouble() / (list.size - ns)
        val goodTime = list.mapNotNull { it.timeGet }.count { it > 0.001 }
	val time = list.mapNotNull { it.timeGet }.sum().toDouble() / goodTime
	val percent = 100.0 * list.mapNotNull { it.percentGet }.sum() / (list.size - ns)
	val f = list.mapNotNull { it.fGet }.sum().toDouble() / (list.size - ns)
	val fMax = list.mapNotNull { it.fGet }.max() ?: 0.0
	val noSol = 100.0 * ns / totalSolutions 
	return E(time, states, edges, percent, f, noSol, fMax)
}

fun eval(list: Iterable<E>): E {
	return E(list.sumByDouble { it.time } / total, list.sumByDouble { it.states } / total, list.sumByDouble { it.edges } / total, list.sumByDouble { it.percent } / total, list.sumByDouble { it.f } / total, list.sumByDouble { it.noSol } / total, list.sumByDouble { it.fMax } / total)
}

fun main(args: Array<String>) {
	val start = "tests_1/test"
	val mapArgs = parseConsoleArguments(args)
	val count = mapArgs.getFirstArg(listOf("-cnt", "--count"), 126) { it[0].toInt() }
	val table = getOrder().take(count).map { position ->
		val test = position.number
		(List(17) { 1003 + it } + List(3) { 10000 + it } + List(20) { 2000 + it } + listOf(20000) + List(20) { 3000 + it }).map { solution ->
			val postfix = if (false/*solution == 20000*//* || (solution >= 3000 && solution < 4000)*/) "_verwer" else ""
			System.err.println("$start$test/info $solution")
			var info = Scanner(File("$start$test/info_machine"))
			val states = info.nextInt()
			val splits = info.nextInt()
			val labels = List(info.nextInt()) { info.next() }
			info.next().toDouble()
			val inf = info.nextInt()
			val edges = states * labels.size + splits
			info.close()
			
			info = Scanner(File("$start$test/solution$solution/result_machine$postfix"))
			val timeGet = q(info.next().toDouble())
			val fGet = q(info.next().toDouble())
			info.next().toDouble()
			info.next().toDouble()
			val percentGet = q(info.next().toDouble())
			info.close()
			var statesGet: Int? = null
			var edgesGet: Int? = null
			if (timeGet != null) {
				info = Scanner(File("$start$test/solution$solution/solution_machine$postfix"))
				statesGet = info.nextInt()
				(0 until statesGet).forEach { _ -> info.next() }
				(0 until info.nextInt()).forEach { _ -> info.next() }
				edgesGet = info.nextInt()
				info.close()
			}
			
			Q(
				states = states,
				symbols = labels.size,
				splits = splits,
				edges = edges, 
				inf = inf,
				timeGet = timeGet,
				fGet = fGet,
				percentGet = percentGet,
				statesGet = statesGet,
				edgesGet = edgesGet,
				testIndex = test,
				solutionIndex = solution
			)
		}
	}.flatten()
	//System.err.println(table.sorted().joinToString(" ") { "${it.testIndex}" })
	//System.err.println(generateSequence { (0..1000000).random() }.take(20).joinToString(" "))
	//print(table.joinToString("\n"))
	val result = table.groupBy { R(it.states, it.symbols, it.splits, it.edges, it.inf) }.mapValues { (_, list) ->
		val inTest = list.groupBy { it.testIndex }
		val inTest20 = inTest.mapValues { (_, value) -> value.filter { it.solutionIndex >= 2000 && it.solutionIndex < 3000 } }
		val inTest30 = inTest.mapValues { (_, value) -> value.filter { (it.solutionIndex >= 1003 && it.solutionIndex < 2000) || (it.solutionIndex >= 10000 && it.solutionIndex < 10100) } }
		val inTestRTI = inTest.mapValues { (_, value) -> value.filter { it.solutionIndex == 20000 } }
		val inTestRTI30 = inTest.mapValues { (_, value) -> value.filter { it.solutionIndex >= 3000 && it.solutionIndex < 4000 } }
		T(eval(inTest20.values.map(::process)), eval(inTest30.values.map(::process)), eval(inTestRTI.values.map(::process)), eval(inTestRTI30.values.map(::process)))
	}.entries.sortedBy { it.key }
	println(result.map { stringify(it.key, it.value) }.joinToString("\n"))
	println()
	println(result.map { stringify1(it.key, it.value) }.joinToString("\n"))
}
