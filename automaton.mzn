int: statesNumber;
set of int: STATES = 1..statesNumber;

int: timersNumber;
set of int: TIMERS = 1..timersNumber;

int: symbolsNumber;
set of int: SYMBOLS = 1..symbolsNumber;

int: samplesNumber;
set of int: SAMPLES = 1..samplesNumber;

int: edgeMaxNumber;
set of int: EDGE_INDEX = 1..edgeMaxNumber;

int: sampleMaxLength;
set of int: SAMPLE_LENGTH = 1..sampleMaxLength;
set of int: EXTENDED_SAMPLE_LENGTH = 0..sampleMaxLength;

array[SAMPLES, SAMPLE_LENGTH] of int: labels;
array[SAMPLES, SAMPLE_LENGTH] of int: times;
array[SAMPLES] of int: sampleLength;

array[STATES, EDGE_INDEX] of var STATES: table;
array[STATES, EDGE_INDEX] of var SYMBOLS: tableSymbols; 
var set of STATES: finals;

int: maxBorderValue = max (sample in SAMPLES) (times[sample, sampleLength[sample]]) + 10;
set of int: CONSTRAINT_DOMEN = 0..maxBorderValue;

array[STATES, EDGE_INDEX, TIMERS] of var CONSTRAINT_DOMEN: leftBorder;
array[STATES, EDGE_INDEX, TIMERS] of var CONSTRAINT_DOMEN: rightBorder;
array[STATES, EDGE_INDEX] of var set of TIMERS: reset;

array[SAMPLES, EXTENDED_SAMPLE_LENGTH] of var STATES: prefixState;
array[SAMPLES, EXTENDED_SAMPLE_LENGTH, TIMERS] of var CONSTRAINT_DOMEN: timeOfTimer;
array[SAMPLES, EXTENDED_SAMPLE_LENGTH, TIMERS] of var CONSTRAINT_DOMEN: timeBeforeTransition;

constraint 
forall (state in STATES, 
        edge  in EDGE_INDEX, 
        timer in TIMERS)
(leftBorder[state, edge, timer] <= rightBorder[state, edge, timer] \/ 
 (leftBorder[state, edge, timer] = 1 /\ rightBorder[state, edge, timer] = 0)) /\
 
forall (state      in STATES, 
        firstEdge  in EDGE_INDEX, 
        secondEdge in EDGE_INDEX
  where firstEdge != secondEdge /\ 
        tableSymbols[state, firstEdge] = tableSymbols[state, secondEdge])
(exists (timer in TIMERS) 
 (rightBorder[state, firstEdge, timer] < leftBorder[state, secondEdge, timer] \/ 
  rightBorder[state, secondEdge, timer] < leftBorder[state, firstEdge, timer])) /\
 
forall (sample           in SAMPLES, 
        positionInSample in 1..sampleLength[sample]) 
(exists (edge in EDGE_INDEX) 
 (forall (timer in TIMERS) 
  (labels[sample, positionInSample] = tableSymbols[prefixState[sample, positionInSample - 1], edge] /\ 
   leftBorder[prefixState[sample, positionInSample - 1], edge, timer] <= timeBeforeTransition[sample, positionInSample - 1, timer] /\ 
   timeBeforeTransition[sample, positionInSample - 1, timer] <= rightBorder[prefixState[sample, positionInSample - 1], edge, timer]))) /\
 
forall (sample           in SAMPLES, 
        positionInSample in 0..(sampleLength[sample] - 1), 
        timer            in TIMERS)
(timeBeforeTransition[sample, positionInSample, timer] = timeOfTimer[sample, positionInSample, timer] + times[sample, positionInSample + 1] - if (positionInSample = 0) then 0 else times[sample, positionInSample] endif) /\

forall (sample           in SAMPLES, 
        positionInSample in 1..sampleLength[sample], 
        edge             in EDGE_INDEX 
  where labels[sample, positionInSample] = tableSymbols[prefixState[sample, positionInSample - 1], edge] /\ 
        forall (timer in TIMERS)
        (leftBorder[prefixState[sample, positionInSample - 1], edge, timer] <= timeBeforeTransition[sample, positionInSample - 1, timer] /\ 
         timeBeforeTransition[sample, positionInSample - 1, timer] <= rightBorder[prefixState[sample, positionInSample - 1], edge, timer]))
(prefixState[sample, positionInSample] = table[prefixState[sample, positionInSample - 1], edge] /\ 
 forall (timer in TIMERS)
 (timeOfTimer[sample, positionInSample, timer] = if timer in reset[prefixState[sample, positionInSample - 1], edge] then 0 else timeBeforeTransition[sample, positionInSample - 1, timer] endif)) /\
 
forall (sample in SAMPLES, 
        timer  in TIMERS)
(timeOfTimer[sample, 0, timer] = 0) /\

forall (sample in SAMPLES)
(prefixState[sample, 0] = 1) /\

forall (sample in SAMPLES)
(prefixState[sample, sampleLength[sample]] in finals);

solve satisfy;

output ["digraph L {\n"] ++ ["\tq\(state)[label=\"\(state)\", " ++ if state in fix(finals) then "color=red" else "" endif ++ "];\n"| state in STATES] ++ [
        "\tq\(state) -> q\(table[state, edge])[label=\"\(tableSymbols[state, edge])\\n" ++ concat(["r(t\(timer))\\n" | timer in fix(reset[state, edge])]) ++ concat(["\(leftBorder[state, edge, timer]) <= t\(timer) <= \(rightBorder[state, edge, timer])\\n" | timer in TIMERS]) ++ "\"];\n"
      | state in STATES, 
        edge  in EDGE_INDEX 
  where forall (timer in TIMERS) 
        (fix(leftBorder[state, edge, timer]) != 1 \/ 
         fix(rightBorder[state, edge, timer]) != 0)] ++ ["}\n"];