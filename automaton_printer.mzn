int: V; % ss number
int: T; % ts number
int: E; % es number

enum S;

array[1..V, 1..E] of 1..V: table;
array[1..V, 1..E] of S: symbols;
array[1..V] of bool: final;

array[1..V, 1..E, 0..T] of int: mn; % min timer value need to have to go by the transition
array[1..V, 1..E, 0..T] of int: mx; % max timer value need to have to go by the transition
array[1..V, 1..E, 0..T] of bool: reset;
array[1..V, 1..E, 0..T] of bool: disTimer;

array[1..V, 1..E] of bool: disEdge;

array[int] of int: ps;
array[int, int] of int: after; % time of some timer directly after transition
array[int, int] of int: before; % time of some timer directly before transition

% bfs

array[1..V, 1..E] of 0..T: minTimer;
array[1..V] of 1..V: vparents;
array[1..V] of 1..E: minEdge;

output let {
  array[int] of int: printVertex  = [s | s in 1..V, e in 1..E where not (disEdge[s, e])];
  array[int] of int: printEdge    = [e | s in 1..V, e in 1..E where not (disEdge[s, e])];
  array[int] of int: finals       = [s | s in 1..V where final[s]];
  array[1..V, 1..E] of set of int: enabledTimers = array2d (1..V, 1..E, [array_union ([ { t } | t in 1..T where not (disTimer[s, e, t])]) | s in 1..V, e in 1..E]);
} in ["\(length (finals)) "] ++ ["\(f) " | f in finals] ++ ["\(length (printVertex))\n"] ++ ["\(printVertex[i]) \(table[printVertex[i], printEdge[i]]) \(symbols[printVertex[i], printEdge[i]]) \(length (enabledTimers[printVertex[i], printEdge[i]])) " ++ concat (["\(t) \(mn[printVertex[i], printEdge[i], t]) \(mx[printVertex[i], printEdge[i], t]) " | t in enabledTimers[printVertex[i], printEdge[i]]]) ++ (let { array[int] of string: resetable = ["\(t) " | t in 1..T where reset[printVertex[i], printEdge[i], t]] } in ("\(length (resetable)) " ++ concat (resetable))) ++ "\n" | i in 1..length (printVertex)];
