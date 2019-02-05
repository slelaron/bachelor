minizinc correct_automaton.mzn data.dzn > graph.dot && sed -i '$ d' graph.dot && dot -Tps graph.dot > graph.ps
