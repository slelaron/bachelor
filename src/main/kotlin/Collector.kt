import java.util.*
import java.io.*
import kotlin.math.*

data class Q1(          val testIndex: Int,
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

const val Tmin = 1.9659

fun est(list: List<Double>): Est {
	val mean = list.sum() / list.size
	val dispersion = list.map { (it - mean).pow(2) }.sum() / list.size
	val S = list.map { (it - mean).pow(2) }.sum() / (list.size - 1)
	
	val r = Tmin * sqrt(S) / sqrt(list.size.toDouble())

	return Est(mean, dispersion, r)
}

data class Est(val mean: Double, val dispersion: Double, val r: Double, val left: Double = mean - r, val right: Double = mean + r) {
	override fun toString() = "${mean.p(2)} ${r.p(2)}"
}

data class E(val time: Est, val states: Est, val edges: Est, val percent: Est, val f: Est, val noSol: Est, val fMax: Est)

data class T(val item20: E, val item30: E, val itemRTI: E, val itemRTI30: E)

fun Double.p(digits: Int) = String.format("%.${digits}f", this)
fun Double.mul() = this * 100

fun stringify(r: R, s: T) = listOf(r.edges, r.states, r.symbols, r.splits, r.inf, 
					s.item20.percent, s.item30.percent, s.itemRTI.percent, s.itemRTI30.percent,
					s.item20.f, s.item30.f, s.itemRTI.f, s.itemRTI30.f,
					s.item20.fMax, s.item30.fMax, s.itemRTI30.fMax).joinToString(" ")

fun stringify1(r: R, s: T) = listOf(r.edges, r.states, r.symbols, r.splits, r.inf, 
					s.item20.noSol, s.item30.noSol, 
					s.item20.time, s.item30.time, s.itemRTI.time, s.itemRTI30.time,
					s.item20.states, s.item30.states, s.itemRTI.states, s.itemRTI30.states,
					s.item20.edges, s.item30.edges, s.itemRTI.edges, s.itemRTI30.edges).joinToString(" ")

fun q1(a: Double): Double? {
	if (a < 0) return null
	return a
}

const val total = 19
const val totalSolutions = 20

fun process(list: List<Q1>): E {
	val states = list.mapNotNull { it.statesGet?.toDouble() }
	val edges = list.mapNotNull { it.edgesGet?.toDouble() }
        val goodTime = list.mapNotNull { it.timeGet }.filter { it > 0.001 }
	val percent = list.mapNotNull { it.percentGet }.map { it * 100.0 }
	val f = list.mapNotNull { it.fGet }
	val fMax = Est(list.mapNotNull { it.fGet }.max() ?: 0.0, 0.0, 0.0)
	val noSol = Est(list.count { it.statesGet == null }.toDouble(), 0.0, 0.0)
	return E(est(goodTime), est(states), est(edges), est(percent), est(f), noSol, fMax)
}

fun meanEst(list: List<Est>) = est(list.map { it.mean })

fun eval(list: List<E>): E {
	val total = list.size
	return E(meanEst(list.map { it.time }), meanEst(list.map { it.states }), meanEst(list.map { it.edges }), 
		meanEst(list.map { it.percent }), meanEst(list.map { it.f }), est(list.map { it.noSol.mean }), est(list.map { it.fMax.mean }))
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
			val timeGet = q1(info.next().toDouble())
			val fGet = q1(info.next().toDouble())
			info.next().toDouble()
			info.next().toDouble()
			val percentGet = q1(info.next().toDouble())
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
			
			Q1(
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
