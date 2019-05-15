int: V; % ss number
int: T; % ts number
int: E; % es number
int: M; % prefix tree es number
int: TC; % max active ts count
int: TE; % max total es

enum S;

enum COL = { W, B, G }; % White - disacceptable, Black - acceptable, Gray - noone knows

array[1..M] of int: labels;
array[1..M] of int: next; % next vertexes
array[1..M] of int: prev; % previous vertexes
array[1..M] of int: times;

int: N = M + 1; % prefix tree vertex number
array[1..N] of COL: acc; % acceptable state or not

array[1..V, 1..E] of var 1..V: table;
array[1..V, 1..E] of var S: symbols;
array[1..V] of var bool: final;

int: inf;
int: volume = pow (inf + 1, T + 1) * length (S);

array[1..V, 1..E, 0..T] of var 0..inf: mn; % min timer value need to have to go by the transition
array[1..V, 1..E, 0..T] of var 0..inf: mx; % max timer value need to have to go by the transition
array[1..V, 1..E, 0..T] of var bool: reset;
array[1..V, 1..E, 0..T] of var bool: disTimer;

array[1..V, 1..E] of var bool: disEdge;

array[1..N] of var 1..V: map;
array[1..N, 0..T] of var 0..inf: after; % time of some timer directly after transition
array[1..M, 0..T] of var 0..inf: before; % time of some timer directly before transition

% bfs

array[1..V] of var 1..V: vparents;
array[1..V] of var 1..E: minEdge;

% Условие, чтобы все выключенные ребра были в конце списка
constraint
forall (s in 1..V,
        e in 1..(E - 1))
(disEdge[s, e] -> disEdge[s, e + 1]);

% Задаем порядок на ребрах. Пусть есть 2 подряд идущих невыключенных ребра.
% Тогда первое ребро имеет либо меньший символ перехода, иначе, при равенстве,
% существует таймер, на котором либо левая граница перехода для данного таймера
% по первому ребру меньше чем по второму, либо, при равенстве, правая граница
% перехода для данного таймера по первому ребру меньше чем по второму, а также
% для всех таймеров с меньшим номером левая и правая граница перехода для данного таймера
% по первому ребру равна левой и правой границе перехода для данного таймера 
% по второму ребру соответственно.
constraint
forall (s in 1..V,
        e in 1..(E - 1))
((not disEdge[s, e]) -> 
 ((not disEdge[s, e + 1]) ->
  symbols[s, e] < symbols[s, e + 1] \/
  (symbols[s, e] = symbols[s, e + 1] /\
   exists (t in 0..T)
   ((mn[s, e, t] < mn[s, e + 1, t] \/
     (mn[s, e, t] == mn[s, e + 1, t] /\
      mx[s, e, t] < mx[s, e + 1, t])) /\
    forall (t0 in 0..T)
    (t0 < t ->
     mn[s, e, t0] == mn[s, e, t0] /\
     mx[s, e, t0] == mx[s, e, t0])))));

% Номер предка всегда меньше номера ребенка
constraint
forall (s in 2..V)
(vparents[s] < s);
     
% Условие, что из предка можно перейти по некоторому ребру в данную вершину,
% причем по меньшим ребрам перейти в данную вершину нельзя и из меньших вершин в данную прийти тоже нельзя.
% Выберем для каждой вершины такое ребро.
constraint
forall (s in 2..V)
(table[vparents[s], minEdge[s]] = s /\
 forall (e in 1..E)
 (e < minEdge[s] -> table[vparents[s], e] != s) /\
 forall (s1 in 1..V)
 (s1 < vparents[s] ->
  forall (e in 1..E)
  (disEdge[s1, e] \/ table[s1, e] != s)));

% Условие, что для двух вершин, первая по номеру меньше второй,
% либо номер предка первой будет меньше номера предка второй,
% либо у них общий предок, и у первой вершины меньше номер вырбанного ребра, чем у второй.
constraint
forall (s1 in 2..V,
        s2 in 2..V
  where s1 < s2)
(vparents[s1] < vparents[s2] \/
 vparents[s1] = vparents[s2] /\
 minEdge[s1] < minEdge[s2]);

%~bfs

% Нулевой таймер не должен сбрасываться ни на каком ребре во временном автомате
constraint
forall (s in 1..V,
        e in 1..E)
(reset[s, e, 0] = false);

% Сужаем область поиска: сразу устанавливаем ограничения, что если ребро не присутствует в данном автомате, то
% его левая граница на все таймеры равна 0, а правая равна 1, все таймеры, проходя по ребру, сбрасываются,
% активны ограничения на все таймеры, ребро ведет в вершину 1, символ перехода равен некоторому, одинаковому для
% всех таких ребер
constraint
forall (s in 1..V,
        e in 1..E)
(disEdge[s, e] ->
 forall (t in 0..T)
 (mn[s, e, t] = 1 /\ mx[s, e, t] = 0) /\
 forall (t in 1..T)
 (reset[s, e, t]) /\
 forall (t in 0..T)
 (disTimer[s, e, t] = false) /\
 table[s, e] = 1 /\
 symbols[s, e] = labels[1]);
 
% Если ребро включено, то левая граница каждого таймера должна быть меньше правой
constraint
forall (s in 1..V,
        e in 1..E,
        t in 0..T)
(disEdge[s, e] \/ mn[s, e, t] <= mx[s, e, t]);
/*
% Полнота: объем области, покрытой всеми таймерами, должен быть равен inf^(T + 1)*|S|
constraint
forall (s in 1..V)
(sum (e in 1..E)
 (if disEdge[s, e] then 0 else product (t in 0..T) (mx[s, e, t] - mn[s, e, t] + 1) endif) = volume);
*/
% Если таймер на данном ребре выключен, то по ребру можно пройти с любым значением таймера, значит левая граница перехода
% по таймеру равна 0, а правая граница равна условной бесконечности
constraint
forall (s in 1..V,
        e in 1..E,
        t in 0..T)
(disTimer[s, e, t] -> mn[s, e, t] = 0 /\ mx[s, e, t] = inf);
 
% Ограничение на детерминизм: из любого состояния по данному символу и значению таймеров существует не более одного перехода.
% Значит для любых двух переходов, присутствующих в автомате, у которых совпадают символы перехода и тип перехода, должен существовать таймер, 
% у которого валидные диапазоны для первого перехода и для второго перехода не пересекаются, иначе говоря, либо нижняя граница первого перехода
% больше верхней границы второго перехода, либо наоборот.
constraint
forall (s  in 1..V,
        e1 in 1..E,
        e2 in 1..E
  where e1 != e2)
(symbols[s, e1] = symbols[s, e2] -> 
 (disEdge[s, e1] \/
  disEdge[s, e2] \/
  exists (t in 0..T) 
  (mx[s, e1, t] < mn[s, e2, t] \/ 
   mx[s, e2, t] < mn[s, e1, t])));

% Предикат: ребру в префиксном дереве соответствует текущее ребро, если
% символ перехода по данному ребру соответствует символ перехода в префиксном дереве,
% тип перехода по данному ребру соответствует тип перехода в префиксном дереве,
% вершина, в которую ведет данное ребро, соответствует вершине, в которую ведет ребро в префиксном дереве,
% выполняются все ограничения на таймеры:
% значение любого таймера сразу перед переходом не меньше нижней границы и не больше верхней границы, а также
% значение таймера сразу после перехода равно 0, если таймер находился во множестве сброса для данного ребра,
% и равно значению таймера сразу перед переходом иначе.
predicate check (1..M: pe, 1..E: e) = 
 symbols[map[prev[pe]], e] = labels[pe] /\
 map[next[pe]] = table[map[prev[pe]], e] /\
 forall (t in 0..T)
 (before[pe, t] >= mn[map[prev[pe]], e, t] /\
  before[pe, t] <= mx[map[prev[pe]], e, t] /\
  after[next[pe], t] = if reset[map[prev[pe]], e, t] then 0 else before[pe, t] endif);

% Ограничение, что для каждого ребра в префиксном дереве существует соответствующее ему ребро во временном автомате
constraint
forall (pe in 1..M)
(exists (e in 1..E)
 (check (pe, e)));

% Ограничение на исключение из рассмотрения ребер, которым не соответствует ни одно из ребер префиксного дерева,
% то есть либо ребро не включено в автомат, либо существует ребро в префиксном дереве, соответствующее данному ребру
constraint
forall (s in 1..V,
        e in 1..E)
(disEdge[s, e] \/
 exists (pe in 1..M)
 (map[prev[pe]] = s -> check (pe, e)));

% Ограничение на связь таймеров вразу после перехода и сразу после перехода:
% таймер сразу до перехода должен увеличиться относительно таймера после перехода
% на значение, являющееся разницей между временем, зафиксированным в текущем ребре префиксного дерева,
% и временем в ребре, являющееся предком данного, в префиксном дереве.
constraint
forall (pe in 1..M,
        t  in 0..T)
(before[pe, t] = after[prev[pe], t] + times[pe]);

% Ограничение, что изначально значение всех таймеров равно 0 (то есть в первой вершине)
constraint
forall (t in 0..T)
(after[1, t] = 0);

% Ограничение, что вершина, соответствующая корню префиксного дерева, является первая вершина в автомате
constraint
map[1] = 1;
/*
% Ограничение, что количество используемых в автомате ребре не превышает максимально допустимого
constraint
sum  (s in 1..V,
      e in 1..E)
(1 - bool2int (disEdge[s, e])) <= TE;

% Ограничение, что количество используемых в автомате таймеров не превышает максимально допустимого
constraint
sum  (s in 1..V,
      e in 1..E,
      t in 0..T)
(1 - bool2int (disTimer[s, e, t] \/ disEdge[s, e])) <= TC;
*/
% Ограничение на принимающие состояния: чтобы состояние было принимающим необходимо и достаточно,
% чтобы существовал лист в префиксном дереве, соответствующий нашей вершине

constraint
forall (s  in 1..V,
        ps in 1..N)
(map[ps] = s -> (acc[ps] = B -> final[s]));

constraint
forall (s  in 1..V,
        ps in 1..N)
(map[ps] = s -> (acc[ps] = W -> (not final[s])));

solve satisfy;
