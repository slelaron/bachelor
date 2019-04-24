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

% Нулевой таймер не должен сбрасываться ни на каком ребре во временном автомате
constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(reset[state, edge, 0] = false);

% Сужаем область поиска: сразу устанавливаем ограничения, что если ребро не присутствует в данном автомате, то
% его левая граница на все таймеры равна 0, а правая равна 1, все таймеры, проходя по ребру сбрасываются, 
% активны ограничения на все таймеры, ребро ведет в вершину 1, символ перехода равен некоторому, одинаковому для
% всех таких ребер, тип символа устанавливаем равным B
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

% Если таймер на данном ребре выключен, то по ребру можно пройти с любым значением таймера, значит левая граница перехода
% по таймеру равна 0, а правая граница равна условной бесконечности
constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber,
        timer in 0..additionalTimersNumber)
(isTimerDisabled[state, edge, timer] -> leftBorder[state, edge, timer] = 0 /\ rightBorder[state, edge, timer] = maxBorderValue);
 
% Ограничение на детерминизм: из любого состояния по данному символу и значению таймеров существует не более одного перехода.
% Значит для любых двух переходов, присутствующих в автомате, у которых совпадают символы перехода и тип перехода, должен существовать таймер, 
% у которого валидные диапазоны для первого перехода и для второго перехода не пересекаются, иначе говоря, либо нижняя граница первого перехода
% больше верхней границы второго перехода, либо наоборот.
constraint
forall (state      in 1..statesNumber,
        firstEdge  in 1..edgeMaxNumber,
        secondEdge in 1..edgeMaxNumber
  where firstEdge != secondEdge)
(tableSymbols[state, firstEdge] = tableSymbols[state, secondEdge] /\
 tableTypes  [state, firstEdge] = tableTypes  [state, secondEdge] -> 
 disabledEdges[state, firstEdge] \/
 disabledEdges[state, secondEdge] \/
 exists (timer in 0..additionalTimersNumber) 
 (rightBorder[state, firstEdge, timer] < leftBorder[state, secondEdge, timer] \/ 
  rightBorder[state, secondEdge, timer] < leftBorder[state, firstEdge, timer]));

% Предикат: ребру в префиксном дереве соответствует текущее ребро, если
% символ перехода по данному ребру соответствует символ перехода в префиксном дереве,
% тип перехода по данному ребру соответствует тип перехода в префиксном дереве,
% вершина, в которую ведет данное ребро, соответствует вершине, в которую ведет ребро в префиксном дереве,
% выполняются все ограничения на таймеры:
% значение любого таймера сразу перед переходом не меньше нижней границы и не больше верхней границы, а также
% значение таймера сразу после перехода равно 0, если таймер находился во множестве сброса для данного ребра,
% и равно значению таймера сразу перед переходом иначе.
predicate transition_check (1..prefixTreeEdgesNumber: prefixTreeEdge, 1..edgeMaxNumber: edge) = 
 tableSymbols[prefixState[prevVertex[prefixTreeEdge]], edge] = labels[prefixTreeEdge] /\
 tableTypes  [prefixState[prevVertex[prefixTreeEdge]], edge] = types [prefixTreeEdge] /\
 prefixState[nextVertex[prefixTreeEdge]] = table[prefixState[prevVertex[prefixTreeEdge]], edge] /\
 forall (timer in 0..additionalTimersNumber)
 (leftBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] <= timeBeforeTransition[nextVertex[prefixTreeEdge], timer] /\
  timeBeforeTransition[nextVertex[prefixTreeEdge], timer] <= rightBorder[prefixState[prevVertex[prefixTreeEdge]], edge, timer] /\
  timeOfTimer[nextVertex[prefixTreeEdge], timer] = if reset[prefixState[prevVertex[prefixTreeEdge]], edge, timer] then 0 else timeBeforeTransition[nextVertex[prefixTreeEdge], timer] endif);

% Ограничение, что для каждого ребра в префиксном дереве существует соответствующее ему ребро во временном автомате
constraint
forall (prefixTreeEdge in 1..prefixTreeEdgesNumber)
(exists (edge in 1..edgeMaxNumber)
 (transition_check (prefixTreeEdge, edge)));

% Ограничение на исключение из рассмотрения ребер, которым не соответствует ни одно из ребер префиксного дерева,
% то есть либо ребро не включено в автомат, либо существует ребро в префиксном дереве, соответствующее данному ребру
constraint
forall (state in 1..statesNumber,
        edge  in 1..edgeMaxNumber)
(disabledEdges[state, edge] \/
 exists (prefixTreeEdge in 1..prefixTreeEdgesNumber
   where prefixState[prevVertex[prefixTreeEdge]] = state)
 (transition_check (prefixTreeEdge, edge)));

% Ограничение на связь таймеров вразу после перехода и сразу после перехода:
% таймер сразу до перехода должен увеличиться относительно таймера после перехода
% на значение, являющееся разницей между временем, зафиксированным в текущем ребре префиксного дерева,
% и временем в ребре, являющееся предком данного, в префиксном дереве.
constraint
forall (prefixTreeEdge in 1..prefixTreeEdgesNumber,
        timer          in 0..additionalTimersNumber)
(timeBeforeTransition[nextVertex[prefixTreeEdge], timer] = timeOfTimer[prevVertex[prefixTreeEdge], timer] + times[prefixTreeEdge] - if prevVertex[prefixTreeEdge] = 1 then 0 else times[parents[prevVertex[prefixTreeEdge]]] endif);

% Ограничение, что изначально значение всех таймеров равно 0 (то есть в первой вершине)
constraint
forall (timer in 0..additionalTimersNumber)
(timeOfTimer[1, timer] = 0);

% Ограничение, что вершина, соответствующая корню префиксного дерева, является первая вершина в автомате
constraint
prefixState[1] = 1;

% Ограничение, что количество используемых в автомате ребре не превышает максимально допустимого
constraint
sum  (state in 1..statesNumber,
      edge  in 1..edgeMaxNumber)
(1 - bool2int (disabledEdges[state, edge])) <= maxTotalEdges;

% Ограничение, что количество используемых в автомате таймеров не превышает максимально допустимого
constraint
sum  (state in 1..statesNumber,
      edge  in 1..edgeMaxNumber,
      timer in 0..additionalTimersNumber)
(1 - bool2int (isTimerDisabled[state, edge, timer] \/ disabledEdges[state, edge])) <= maxActiveTimersCount;

% Ограничение на принимающие состояния: чтобы состояние было принимающим необходимо и достаточно,
% чтобы существовал лист в префиксном дереве соответствующей нашей вершине
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

% Попытка решения сразу с минимизацией суммарной длины используемых ограничений
solve minimize (sum (state in 1..statesNumber,
                     edge  in 1..edgeMaxNumber
               where not (disabledEdges[state, edge]))
                (sum (timer in 0..additionalTimersNumber
               where not (isTimerDisabled[state, edge, timer])) 
                 (rightBorder[state, edge, timer] - leftBorder[state, edge, timer])));
                 
%solve satisfy;