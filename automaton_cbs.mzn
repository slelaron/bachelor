int: statesNumber;
int: additionalTimersNumber;
int: edgeMaxNumber;
int: prefixTreeEdgesNumber;
int: maxActiveTimersCount;
int: maxTotalEdges;

enum SYMBOLS;
enum TYPES = { B, E };

array[1..prefixTreeEdgesNumber] of int: labels;
array[1..prefixTreeEdgesNumber] of TYPES: types;
array[1..prefixTreeEdgesNumber] of int: nextVertex;
array[1..prefixTreeEdgesNumber] of int: prevVertex;
array[1..prefixTreeEdgesNumber] of int: times;

int: prefixTreeVertexNumber = length (array_union ([ { prevVertex[edge], nextVertex[edge] } | edge in 1..prefixTreeEdgesNumber]));

array[2..prefixTreeVertexNumber] of 1..prefixTreeEdgesNumber: parents = array1d (2..prefixTreeVertexNumber, [edge | vertex in 1..prefixTreeVertexNumber, edge in 1..prefixTreeEdgesNumber where nextVertex[edge] = vertex]);

array[1..prefixTreeVertexNumber] of bool: isPrefixTreeLeaf = [not (exists (edge in 1..prefixTreeEdgesNumber) (prevVertex[edge] = vertex)) | vertex in 1..prefixTreeVertexNumber];

array[1..statesNumber, 1..edgeMaxNumber] of var 1..statesNumber: table;
array[1..statesNumber, 1..edgeMaxNumber] of var SYMBOLS: tableSymbols;
array[1..statesNumber, 1..edgeMaxNumber] of var TYPES: tableTypes;
array[1..statesNumber] of var bool: isFinal;

int: maxBorderValue = max (edge in 1..prefixTreeEdgesNumber) (times[edge]) + 10;

array[1..statesNumber, 1..edgeMaxNumber, 0..additionalTimersNumber] of var 0..maxBorderValue: leftBorder;
array[1..statesNumber, 1..edgeMaxNumber, 0..additionalTimersNumber] of var 0..maxBorderValue: rightBorder;
array[1..statesNumber, 1..edgeMaxNumber, 0..additionalTimersNumber] of var bool: reset;
array[1..statesNumber, 1..edgeMaxNumber, 0..additionalTimersNumber] of var bool: isTimerDisabled;

array[1..statesNumber, 1..edgeMaxNumber] of var bool: disabledEdges;

array[1..prefixTreeVertexNumber] of var 1..statesNumber: prefixState;
array[1..prefixTreeVertexNumber, 0..additionalTimersNumber] of var 0..maxBorderValue: timeOfTimer;
array[1..prefixTreeVertexNumber, 0..additionalTimersNumber] of var 0..maxBorderValue: timeBeforeTransition;


% temporary

constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber,
        timer in 0..additionalTimersNumber)
(isTimerDisabled[state, edge, timer] = false);

%~temporary

% cbs

array[1..statesNumber] of var 0..statesNumber: balance;
array[1..statesNumber, 0..statesNumber] of var SYMBOLS: balanceStack;

%~cbs

constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(reset[state, edge, 0] = false);

constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(disabledEdges[state, edge] ->
 forall (timer in 0..additionalTimersNumber)
 (leftBorder[state, edge, timer] = 1 /\ rightBorder[state, edge, timer] = 0) /\
 forall (timer in 1..additionalTimersNumber)
 (reset[state, edge, timer]) /\
 forall (timer in 0..additionalTimersNumber)
 (isTimerDisabled[state, edge, timer] = false) /\
 table[state, edge] = 1 /\
 tableSymbols[state, edge] = labels[1] /\
 tableTypes  [state, edge] = B);
 
constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber,
        timer in 0..additionalTimersNumber)
(isTimerDisabled[state, edge, timer] -> leftBorder[state, edge, timer] = 0 /\ rightBorder[state, edge, timer] = maxBorderValue);
 
constraint
forall (state      in 1..statesNumber,
        firstEdge  in 1..edgeMaxNumber,
        secondEdge in 1..edgeMaxNumber
  where firstEdge != secondEdge /\ 
        tableSymbols[state, firstEdge] = tableSymbols[state, secondEdge] /\
        tableTypes  [state, firstEdge] = tableTypes  [state, secondEdge])
(disabledEdges[state, firstEdge] \/
 disabledEdges[state, secondEdge] \/
 exists (timer in 0..additionalTimersNumber) 
 (rightBorder[state, firstEdge, timer] < leftBorder[state, secondEdge, timer] \/ 
  rightBorder[state, secondEdge, timer] < leftBorder[state, firstEdge, timer]));

predicate transition_check (1..prefixTreeEdgesNumber: prefixTreeEdge, 1..edgeMaxNumber: edge) = 
 tableSymbols[prefixState[prevVertex[prefixTreeEdge]], edge] = labels[prefixTreeEdge] /\
 tableTypes  [prefixState[prevVertex[prefixTreeEdge]], edge] = types [prefixTreeEdge] /\
 prefixState[nextVertex[prefixTreeEdge]] = table[prefixState[prevVertex[prefixTreeEdge]], edge] /\
 forall (timer in 0..additionalTimersNumber)
 (leftBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] <= timeBeforeTransition[nextVertex[prefixTreeEdge], timer] /\
  timeBeforeTransition[nextVertex[prefixTreeEdge], timer] <= rightBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] /\
  timeOfTimer[nextVertex[prefixTreeEdge], timer] = if reset[prefixState[prevVertex[prefixTreeEdge]], edge, timer] then 0 else timeBeforeTransition[nextVertex[prefixTreeEdge], timer] endif);

constraint
forall (prefixTreeEdge in 1..prefixTreeEdgesNumber)
(exists (edge in 1..edgeMaxNumber)
 (transition_check (prefixTreeEdge, edge)));
 
constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(disabledEdges[state, edge] \/
 exists (prefixTreeEdge in 1..prefixTreeEdgesNumber
   where prefixState[prevVertex[prefixTreeEdge]] = state)
 (transition_check (prefixTreeEdge, edge)));

constraint
forall (prefixTreeEdge in 1..prefixTreeEdgesNumber,
        timer          in 0..additionalTimersNumber)
(timeBeforeTransition[nextVertex[prefixTreeEdge], timer] = timeOfTimer[prevVertex[prefixTreeEdge], timer] + times[prefixTreeEdge] - if prevVertex[prefixTreeEdge] = 1 then 0 else times[parents[prevVertex[prefixTreeEdge]]] endif);

constraint
forall (timer in 0..additionalTimersNumber)
(timeOfTimer[1, timer] = 0);

constraint
prefixState[1] = 1;

constraint
sum  (state in 1..statesNumber,
      edge  in 1..edgeMaxNumber)
(1 - bool2int (disabledEdges[state, edge])) <= maxTotalEdges;

constraint
sum  (state in 1..statesNumber,
      edge  in 1..edgeMaxNumber,
      timer in 0..additionalTimersNumber
where (not disabledEdges[state, edge]))
(1 - bool2int (isTimerDisabled[state, edge, timer])) <= maxActiveTimersCount;

constraint
forall (state in 1..statesNumber)
(isFinal[state] <-> (exists (prefixTreeVertex in 1..prefixTreeVertexNumber) 
                     (prefixState[prefixTreeVertex] = state /\ isPrefixTreeLeaf[prefixTreeVertex])));

% cbs

constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(disabledEdges[state, edge] \/ 
 (if tableTypes[state, edge] = B then
   balance[table[state, edge]] = balance[state] + 1 /\
   forall (position in 1..statesNumber)
   (if     position < balance[table[state, edge]] then balanceStack[table[state, edge], position] = balanceStack[state, position]
    elseif position = balance[table[state, edge]] then balanceStack[table[state, edge], position] = tableSymbols[state, edge]
    else                                               balanceStack[table[state, edge], position] = labels[1]
    endif)
  else
   balance[table[state, edge]] = balance[state] - 1 /\
   balanceStack[state, balance[state]] = tableSymbols[state, edge] /\
   forall (position in 1..statesNumber)
   (if position < balance[state] then balanceStack[table[state, edge], position] = balanceStack[state, position]
    else                              balanceStack[table[state, edge], position] = labels[1]
    endif)
  endif));

constraint
balance[1] = 0 /\
forall (position in 1..statesNumber)
(balanceStack[1, position] = labels[1]);

constraint
forall (state in 1..statesNumber)
(isFinal[state] -> balance[state] = 0);

%~cbs

solve minimize (sum (state in 1..statesNumber,
                     edge  in 1..edgeMaxNumber
               where not (disabledEdges[state, edge]))
                (sum (timer in 0..additionalTimersNumber
               where not (isTimerDisabled[state, edge, timer])) 
                 (rightBorder[state, edge, timer] - leftBorder[state, edge, timer])));
                 
%solve satisfy;