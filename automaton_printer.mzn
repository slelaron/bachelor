int: V; % ss number
int: T; % ts number
int: E; % es number

enum S;

array[1..V, 1..E] of int: table;
array[1..V, 1..E] of int: symbols;
array[1..V] of bool: final;

array[1..V, 1..E, 1..T] of int: mn; % min timer value need to have to go by the transition
array[1..V, 1..E, 1..T] of int: mx; % max timer value need to have to go by the transition
array[1..V, 1..E, 1..T] of bool: reset;
array[1..V, 1..E, 1..T] of bool: disTimer;

array[int] of int: map;
array[int, int] of int: after; % time of some timer directly after transition
array[int, int] of int: before; % time of some timer directly before transition

% bfs

array[1..V] of int: parents;
array[1..V] of int: minEdge;

output let {
  array[int] of int: printVertex  = [s | s in 1..V, e in 1..E where symbols[s, e] != 0];
  array[int] of int: printEdge    = [e | s in 1..V, e in 1..E where symbols[s, e] != 0];
  array[int] of int: finals       = [s | s in 1..V where final[s]];
  array[1..V, 1..E] of set of int: enabledTimers = array2d (1..V, 1..E, [array_union ([ { t } | t in 1..T where not (disTimer[s, e, t])]) | s in 1..V, e in 1..E]);
} in ["\(V)\n"] ++ ["q\(v) " | v in 1..V] ++ ["\n\(length (finals)) "] ++ ["\(f) " | f in finals] ++ ["\(length (printVertex))\n"] ++ ["q\(printVertex[i]) q\(table[printVertex[i], printEdge[i]]) \(to_enum(S, symbols[printVertex[i], printEdge[i]])) \(length (enabledTimers[printVertex[i], printEdge[i]])) " ++ concat (["\(t) \(mn[printVertex[i], printEdge[i], t]) \(mx[printVertex[i], printEdge[i], t]) " | t in enabledTimers[printVertex[i], printEdge[i]]]) ++ (let { array[int] of string: resetable = ["\(t) " | t in 1..T where reset[printVertex[i], printEdge[i], t]] } in ("\(length (resetable)) " ++ concat (resetable))) ++ "\n" | i in 1..length (printVertex)];
