int: statesNumber;
set of int: STATES = 1..statesNumber;

int: additionalTimersNumber;
set of int: TIMERS = 0..additionalTimersNumber;

enum SYMBOLS;

int: edgeMaxNumber;
set of int: EDGE_INDEX = 1..edgeMaxNumber;

array[STATES, EDGE_INDEX] of STATES: table;
array[STATES, EDGE_INDEX] of SYMBOLS: tableSymbols;
array[STATES] of bool: isFinal;

array[STATES, EDGE_INDEX, TIMERS] of int: leftBorder;
array[STATES, EDGE_INDEX, TIMERS] of int: rightBorder;
array[STATES, EDGE_INDEX, TIMERS] of bool: reset;

array[STATES, EDGE_INDEX] of bool: disabledEdges;

array[int] of STATES: prefixState;
array[int, int] of int: timeOfTimer;
array[int, int] of int: timeBeforeTransition;

output let {
  array[int] of int: printVertex = [state | state in STATES, edge in EDGE_INDEX where not (disabledEdges[state, edge])];
  array[int] of int: printEdge   = [edge  | state in STATES, edge in EDGE_INDEX where not (disabledEdges[state, edge])];
  array[int] of int: finalsArr   = [state | state in STATES where isFinal[state]];
} in ["\(length(finalsArr)) "] ++ ["\(final) " | final in finalsArr] ++ ["\(length (printVertex))\n"] ++ ["\(printVertex[index]) \(table[printVertex[index], printEdge[index]]) \(tableSymbols[printVertex[index], printEdge[index]]) " ++ concat (["\(leftBorder[printVertex[index], printEdge[index], timer]) \(rightBorder[printVertex[index], printEdge[index], timer]) " | timer in TIMERS]) ++ (let { array[int] of string: resetable = ["\(timer) " | timer in TIMERS where reset[printVertex[index], printEdge[index], timer]] } in ("\(length (resetable)) " ++ concat (resetable))) ++ "\n" | index in 1..length (printVertex)];