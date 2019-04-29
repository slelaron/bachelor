int: statesNumber;
set of int: STATES = 1..statesNumber;

int: additionalTimersNumber;
set of int: TIMERS = 0..additionalTimersNumber;

enum SYMBOLS;
enum TYPES = { B, E };

int: edgeMaxNumber;
set of int: EDGE_INDEX = 1..edgeMaxNumber;

array[STATES, EDGE_INDEX] of STATES: table;
array[STATES, EDGE_INDEX] of SYMBOLS: tableSymbols;
array[STATES, EDGE_INDEX] of TYPES: tableTypes;
array[STATES] of bool: isFinal;

array[STATES, EDGE_INDEX, TIMERS] of int: leftBorder;
array[STATES, EDGE_INDEX, TIMERS] of int: rightBorder;
array[STATES, EDGE_INDEX, TIMERS] of bool: reset;
array[STATES, EDGE_INDEX, TIMERS] of bool: isTimerDisabled;

array[STATES, EDGE_INDEX] of bool: disabledEdges;

array[int] of STATES: prefixState;
array[int, int] of int: timeOfTimer;
array[int, int] of int: timeBeforeTransition;

% cbs

array[1..statesNumber] of var 0..statesNumber: balance;
array[1..statesNumber, 0..statesNumber] of var SYMBOLS: balanceStack;

%~cbs

% bfs

array[1..statesNumber, 1..edgeMaxNumber] of var 0..additionalTimersNumber: timerMin;
array[1..statesNumber] of var 1..statesNumber: parentInOrder;
array[1..statesNumber] of var 1..edgeMaxNumber: edgeMin;

%~bfs

output let {
  array[int] of int: printVertex  = [state | state in STATES, edge in EDGE_INDEX where not (disabledEdges[state, edge])];
  array[int] of int: printEdge    = [edge  | state in STATES, edge in EDGE_INDEX where not (disabledEdges[state, edge])];
  array[int] of int: finals       = [state | state in STATES where isFinal[state]];
  array[STATES, EDGE_INDEX] of set of int: enabledTimers = array2d (STATES, EDGE_INDEX, [array_union ([ { timer } | timer in TIMERS where not (isTimerDisabled[state, edge, timer])]) | state in STATES, edge in EDGE_INDEX]);
} in ["\(length (finals)) "] ++ ["\(final) " | final in finals] ++ ["\(length (printVertex))\n"] ++ ["\(printVertex[index]) \(table[printVertex[index], printEdge[index]]) \(tableSymbols[printVertex[index], printEdge[index]]) \(tableTypes[printVertex[index], printEdge[index]]) \(length (enabledTimers[printVertex[index], printEdge[index]])) " ++ concat (["\(timer) \(leftBorder[printVertex[index], printEdge[index], timer]) \(rightBorder[printVertex[index], printEdge[index], timer]) " | timer in enabledTimers[printVertex[index], printEdge[index]]]) ++ (let { array[int] of string: resetable = ["\(timer) " | timer in TIMERS where reset[printVertex[index], printEdge[index], timer]] } in ("\(length (resetable)) " ++ concat (resetable))) ++ "\n" | index in 1..length (printVertex)];