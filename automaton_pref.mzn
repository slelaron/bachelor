int: statesNumber;
set of int: STATES = 1..statesNumber;

int: additionalTimersNumber;
set of int: TIMERS = 0..additionalTimersNumber;
set of int: TIMERS_CAN_BE_RESETED = 1..additionalTimersNumber;

enum SYMBOLS;

int: edgeMaxNumber;
set of int: EDGE_INDEX = 1..edgeMaxNumber;

int: prefixTreeEdgesNumber;
set of int: PREFIX_TREE_EDGES = 1..prefixTreeEdgesNumber;

array[PREFIX_TREE_EDGES] of int: labels;
array[PREFIX_TREE_EDGES] of int: nextVertex;
array[PREFIX_TREE_EDGES] of int: prevVertex;
array[PREFIX_TREE_EDGES] of int: times;

int: prefixTreeVertexNumber = length (array_union ([ { prevVertex[edge], nextVertex[edge] } | edge in PREFIX_TREE_EDGES]));
set of int: PREFIX_TREE_VERTEXES = 1..prefixTreeVertexNumber;
set of int: TRIMMED_PREFIX_TREE_VERTEXES = 2..prefixTreeVertexNumber;

array[TRIMMED_PREFIX_TREE_VERTEXES] of PREFIX_TREE_EDGES: parents = array1d (TRIMMED_PREFIX_TREE_VERTEXES, [edge | vertex in PREFIX_TREE_VERTEXES, edge in PREFIX_TREE_EDGES where nextVertex[edge] = vertex]);
array[PREFIX_TREE_VERTEXES] of set of PREFIX_TREE_EDGES: prefixTree = [array_union ([ { edge } | edge in PREFIX_TREE_EDGES where vertex = prevVertex[edge]]) | vertex in PREFIX_TREE_VERTEXES];

set of int: prefixTreeLeafs = array_union ([ { vertex } | vertex in PREFIX_TREE_VERTEXES where not (exists (edge in PREFIX_TREE_EDGES) (prevVertex[edge] = vertex))]);

array[STATES, EDGE_INDEX] of var STATES: table;
array[STATES, EDGE_INDEX] of var SYMBOLS: tableSymbols;
var set of STATES: finals;

int: maxBorderValue = max (edge in PREFIX_TREE_EDGES) (times[edge]) + 10;
set of int: CONSTRAINT_DOMAIN = 0..maxBorderValue;

var int: maxBorderValueAnother;
var int: prefixTreeVertexNumberAnother;

array[STATES, EDGE_INDEX, TIMERS] of var CONSTRAINT_DOMAIN: leftBorder;
array[STATES, EDGE_INDEX, TIMERS] of var CONSTRAINT_DOMAIN: rightBorder;
array[STATES, EDGE_INDEX] of var set of TIMERS_CAN_BE_RESETED: reset;

array[PREFIX_TREE_VERTEXES] of var STATES: prefixState;
array[PREFIX_TREE_VERTEXES, TIMERS] of var CONSTRAINT_DOMAIN: timeOfTimer;
array[PREFIX_TREE_VERTEXES, TIMERS] of var CONSTRAINT_DOMAIN: timeBeforeTransition;

constraint
maxBorderValueAnother = maxBorderValue;

constraint
prefixTreeVertexNumberAnother = prefixTreeVertexNumber;

constraint
forall (prefixTreeEdge in PREFIX_TREE_EDGES)
(assert (prefixTreeEdge in prefixTree[prevVertex[prefixTreeEdge]] /\ 
         prefixTreeEdge =  parents   [nextVertex[prefixTreeEdge]], "parents and prefixTree has incompatible data"));

constraint 
forall (state in STATES,
        edge  in EDGE_INDEX,
        timer in TIMERS)
(leftBorder[state, edge, timer] <= rightBorder[state, edge, timer] \/ 
 (leftBorder[state, edge, timer] = 1 /\ rightBorder[state, edge, timer] = 0));
 
constraint
forall (state      in STATES,
        firstEdge  in EDGE_INDEX,
        secondEdge in EDGE_INDEX
  where firstEdge != secondEdge /\ 
        tableSymbols[state, firstEdge] = tableSymbols[state, secondEdge])
(exists (timer in TIMERS) 
 ((leftBorder[state, firstEdge, timer] = 1 /\ rightBorder[state, firstEdge, timer] = 0) \/
  (leftBorder[state, secondEdge, timer] = 1 /\ rightBorder[state, secondEdge, timer] = 0) \/
  rightBorder[state, firstEdge, timer] < leftBorder[state, secondEdge, timer] \/ 
  rightBorder[state, secondEdge, timer] < leftBorder[state, firstEdge, timer]));
 
constraint
forall (prefixTreeEdge in PREFIX_TREE_EDGES)
(exists (edge in EDGE_INDEX)
 (tableSymbols[prefixState[prevVertex[prefixTreeEdge]], edge] = labels[prefixTreeEdge] /\
  prefixState[nextVertex[prefixTreeEdge]] = table[prefixState[prevVertex[prefixTreeEdge]], edge] /\
  forall (timer in TIMERS)
  (leftBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] <= timeBeforeTransition[nextVertex[prefixTreeEdge], timer] /\
   timeBeforeTransition[nextVertex[prefixTreeEdge], timer] <= rightBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] /\
   timeOfTimer[nextVertex[prefixTreeEdge], timer] = if timer in reset[prefixState[prevVertex[prefixTreeEdge]], edge] then 0 else timeBeforeTransition[nextVertex[prefixTreeEdge], timer] endif)));

constraint
forall (prefixTreeEdge in PREFIX_TREE_EDGES,
        timer          in TIMERS)
(timeBeforeTransition[nextVertex[prefixTreeEdge], timer] = timeOfTimer[prevVertex[prefixTreeEdge], timer] + times[prefixTreeEdge] - if (prevVertex[prefixTreeEdge] = 1) then 0 else times[parents[prevVertex[prefixTreeEdge]]] endif);

constraint
forall (timer in TIMERS)
(timeOfTimer[1, timer] = 0);

constraint
prefixState[1] = 1;

constraint
forall (state in STATES)
(state in finals <-> (exists (prefixTreeVertex in PREFIX_TREE_VERTEXES) 
                      (prefixState[prefixTreeVertex] = state /\ prefixTreeVertex in prefixTreeLeafs)));

solve satisfy;