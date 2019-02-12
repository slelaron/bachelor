int: statesNumber;
set of int: STATES = 1..statesNumber;

int: additionalTimersNumber;
set of int: TIMERS = 0..additionalTimersNumber;
set of int: TIMERS_CAN_BE_RESETED = 1..additionalTimersNumber;

enum SYMBOLS;

int: edgeMaxNumber;
set of int: EDGE_INDEX = 1..edgeMaxNumber;

array[STATES, EDGE_INDEX] of STATES: table;
array[STATES, EDGE_INDEX] of SYMBOLS: tableSymbols;
set of STATES: finals;

int: maxBorderValueAnother;
set of int: CONSTRAINT_DOMAIN = 0..maxBorderValueAnother;

int: prefixTreeVertexNumberAnother;
set of int: PREFIX_TREE_VERTEXES = 1..prefixTreeVertexNumberAnother;

array[STATES, EDGE_INDEX, TIMERS] of CONSTRAINT_DOMAIN: leftBorder;
array[STATES, EDGE_INDEX, TIMERS] of CONSTRAINT_DOMAIN: rightBorder;
array[STATES, EDGE_INDEX] of set of TIMERS_CAN_BE_RESETED: reset;

array[PREFIX_TREE_VERTEXES] of STATES: prefixState;
array[PREFIX_TREE_VERTEXES, TIMERS] of CONSTRAINT_DOMAIN: timeOfTimer;
array[PREFIX_TREE_VERTEXES, TIMERS] of CONSTRAINT_DOMAIN: timeBeforeTransition;

output let {
  array[int] of int: printVertex = [state | state in STATES, edge in EDGE_INDEX where forall(timer in TIMERS) (leftBorder[state, edge, timer] != 1 \/ rightBorder[state, edge, timer] != 0)];
  array[int] of int: printEdge   = [edge  | state in STATES, edge in EDGE_INDEX where forall(timer in TIMERS) (leftBorder[state, edge, timer] != 1 \/ rightBorder[state, edge, timer] != 0)];
  array[int] of int: finalsArr = [final | final in finals];
} in ["\(length(finalsArr)) "] ++ ["\(final) " | final in finalsArr] ++ ["\(length (printVertex))\n"] ++ ["\(printVertex[index]) \(table[printVertex[index], printEdge[index]]) \(tableSymbols[printVertex[index], printEdge[index]]) " ++ concat (["\(leftBorder[printVertex[index], printEdge[index], timer]) \(rightBorder[printVertex[index], printEdge[index], timer]) " | timer in TIMERS]) ++ (let { array[int] of string: resetable = ["\(timer) " | timer in reset[printVertex[index], printEdge[index]]] } in ("\(length (resetable)) " ++ concat (resetable))) ++ "\n" | index in 1..length (printVertex)];