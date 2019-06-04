import java.util.*
import java.io.*
import kotlin.math.roundToInt

data class Q(val states: Int,
			 val symbols: Int,
			 val splits: Int,
			 val edges: Int,
			 val inf: Int,
			 val time20: Double?,
			 val states20: Int?,
			 val edges20: Int?,
			 val percent20: Double?,
			 val f20: Double?,
			 val time30: Double?,
			 val states30: Int?,
			 val edges30: Int?,
			 val percent30: Double?,
			 val f30: Double?,
			 val timeRTI: Double?,
			 val statesRTI: Int?,
			 val edgesRTI: Int?,
			 val percentRTI: Double?,
			 val fRTI: Double?) {

	private fun Double.p(digits: Int) = String.format("%.${digits}f", this)

	private fun Double.mul() = this * 100

	override fun toString() =
	listOf(states, symbols, splits, edges, inf, time20?.roundToInt(), states20, edges20, percent20?.mul()?.p(1),
		f20?.p(2), time30?.roundToInt(), states30, edges30, percent30?.mul()?.p(1), f30?.p(2), timeRTI?.roundToInt(), statesRTI,
		edgesRTI, percentRTI?.mul()?.p(1), fRTI?.p(2)).joinToString(" & ", postfix = """ \\\hline""")
		{ if (it == null) "--" else "$it" }
}

fun q(a: Double): Double? {
	if (a < 0) return null
	return a
}


fun main() {
	val start = "bachelor/tests_1/test"	
	val start1 = "another/$start"
	val table = Array(125) { j ->
		val i = if (j + 1 >= 108) j + 2 else j + 1
		System.err.println("$start$i/info")
		var info = Scanner(File("$start$i/info_machine"))
		val states = info.nextInt()
		val splits = info.nextInt()
		val labels = List(info.nextInt()) { info.next() }
		info.next().toDouble()
		val inf = info.nextInt()
		val edges = states * labels.size + splits
		info.close()
		
		info = Scanner(File("$start1$i/solution500/result_machine"))
		val time20 = q(info.next().toDouble())
		val f20 = q(info.next().toDouble())
		info.next().toDouble()
		info.next().toDouble()
		val percent20 = q(info.next().toDouble())
		info.close()
		var states20: Int? = null
		var edges20: Int? = null
		if (time20 != null) {
			info = Scanner(File("$start1$i/solution500/solution_machine"))
			states20 = info.nextInt()
			(0 until states20).forEach { _ -> info.next() }
			(0 until info.nextInt()).forEach { _ -> info.next() }
			edges20 = info.nextInt()
			info.close()
		}

		info = Scanner(File("$start$i/solution501/result_machine"))
		val time30 = q(info.next().toDouble())
		val f30 = q(info.next().toDouble())
		info.next().toDouble()
		info.next().toDouble()
		val percent30 = q(info.next().toDouble())
		info.close()
		var states30: Int? = null
		var edges30: Int? = null
		if (time30 != null) {
			System.err.println("$time30")
			info = Scanner(File("$start$i/solution501/solution_machine"))
			states30 = info.nextInt()
			(0 until states30).forEach { _ -> info.next() }
			(0 until info.nextInt()).forEach { _ -> info.next() }
			edges30 = info.nextInt()
			info.close()
		}
		
		
		info = Scanner(File("$start$i/solution100/result_machine_verwer"))
		val timeRTI = q(info.next().toDouble())
		val fRTI = q(info.next().toDouble())
		info.next().toDouble()
		info.next().toDouble()
		val percentRTI = q(info.next().toDouble())
		info.close()
		var statesRTI: Int? = null
		var edgesRTI: Int? = null
		if (timeRTI != null) {
			info = Scanner(File("$start$i/solution100/solution_machine_verwer"))
			statesRTI = info.nextInt()
			(0 until statesRTI).forEach { _ -> info.next() }
			(0 until info.nextInt()).forEach { _ -> info.next() }
			edgesRTI = info.nextInt()
			info.close()
		}
		
		Q(
			states = states,
			symbols = labels.size,
			splits = splits,
			edges = edges, 
			inf = inf,
			time20 = time20,
			f20 = f20,
			percent20 = percent20,
			states20 = states20,
			edges20 = edges20,
			time30 = time30,
			f30 = f30,
			percent30 = percent30,
			states30 = states30,
			edges30 = edges30,
			timeRTI = timeRTI,
			fRTI = fRTI,
			percentRTI = percentRTI,
			statesRTI = statesRTI,
			edgesRTI = edgesRTI
				
		)
				
	}
	print(table.joinToString("\n"))
}
