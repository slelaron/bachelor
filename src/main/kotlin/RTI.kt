fun buildTAPTA(traces: Iterable<Trace>, inf: Int = Int.MAX_VALUE): RTA {
    val automaton = RTA(number = RTA.next++)
    automaton.addTraces(traces, inf = inf)
    return automaton
}

fun rti(traces: Iterable<Trace>, inf: Int = Int.MAX_VALUE): RTA {
    val automaton = buildTAPTA(traces, inf)
    automaton.color()
    val red = mutableListOf(automaton)
    var now = 1
    val blueWithRed = mutableMapOf<Long, MutableSet<Long>>()
    while (true) {
        if (!automaton.isConsistent()) {
            throw Exception("Non-consistent automaton")
        }
        val redNames = red.map { it.name }.toSet()
        //automaton.createDotFile("debug/debug$now", inf = inf)
        System.err.println("Step = ${now++}")
        clearRecordings()
        val possible = mutableListOf<Pair<Int, () -> Unit>>()
        val blue = red.flatMap {
            it.ways.entries.asSequence().zip(generateSequence { it }).toList()
        }.filter { (edge, _) ->
            edge.value.second.name !in redNames
        }.groupBy({ (edge, _) ->
            edge.value.second
        }) { (edge, from) ->
            from to edge.key
        }.mapValues { (key, value) ->
            if (value.size != 1) throw Exception("not one path to ${key.name}: ${value.map { it.first.name to it.second }}")
            value.first()
        }
        if (blue.isEmpty()) break
        //System.err.println("StartMerge")
        val measure = automaton.consistentMeasure()
        for (r in red) {
            for (b in blue) {
                val redNumber = r.number
                val blueNumber = b.key.number
                if (redNumber in blueWithRed.getOrPut(blueNumber) { mutableSetOf() }) {
                    //System.err.println("Skip")
                    continue
                }
                //System.err.println("Try: ${r.name} ${b.key.name}")
                val key = AutomatonEdge(b.value.first, b.key, b.value.second, RTA.oneTimerSet)
                val marker = getMarker()
                val res = automaton.merge(r, key, inf = inf, needEdgeCorrection = false)
                //val consistency = automaton.isConsistent()
                //System.err.println("q$redNumber q$blueNumber: merge = $res, consistency = $consistency")
                if (res && automaton.isConsistent()) {
                    /*if (redNumber in blueWithRed.getOrPut(blueNumber) { mutableSetOf() }) {
                        throw Exception("Wrong idea: red = q$redNumber, blue = q$blueNumber")
                    }*/
                    possible += 3 * automaton.consistentMeasure() + 2 to {
                        System.err.println("Merge ${r.name} ${b.key.name}")
                        val r = automaton.merge(r, key, inf = inf, needEdgeCorrection = true)
                    }
                } else/* if (!res)*/ {
                    if (redNumber != r.number) {
                        throw Exception("Numbers changing $redNumber != ${r.number}")
                    }
                    blueWithRed.getOrPut(blueNumber) { mutableSetOf() } += redNumber
                }
                undo(marker)
            }
        }
        //System.err.println("EndMerge")
        //System.err.println("StartSplit")
        for (r in red) {
            for ((cond, tails) in r.tails.toMap()) {
                val to = r.ways[cond]?.second ?: throw Exception("No such transition $cond")
                if (!to.isRed) {
                    val sortedTimes = tails.map { it.records.firstOrNull()?.time ?: throw Exception("Empty trace") }.
                            distinct().sorted().dropLast(1)
                    val range = cond.timeGuards[1] ?: throw Exception("1st timer doesn't exist")
                    //System.err.println("Range: $range")
                    //System.err.println(sortedTails)
                    for (time in sortedTimes) {
                        val marker = getMarker()
                        r.split(cond.label, range, time, inf = inf)
                        possible += 3 * automaton.consistentMeasure() + 1 to {
                            System.err.println("Split ${cond.label} $range at $time")
                            r.split(cond.label, range, time, inf = inf)
                        }
                        undo(marker)
                    }
                }
            }
        }
        //System.err.println("EndSplit")
        //System.err.println("StartColor")
        for (b in blue) {
            val marker = getMarker()
            val result = b.key.color()
            if (result) {
                possible += 3 * measure to {
                    System.err.println("Color ${b.key.name}")
                    red += b.key
                    val color = b.key.color()
                }
            }
            undo(marker)
        }
        //System.err.println("EndColor")
        val operation = possible.maxBy { it.first }?.second ?: throw Exception("Can't perform any operation $possible")
        operation()
    }
    //automaton.createDotFile("debug/result")
    return automaton
}
