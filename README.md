# Renamable Horn heuristic for cube-and-conquer

SelectVar(F) :
Decision heuristic: Find the maximum renamable-Horn sub-formula F_r of a CNF F . 
Select a decision variable from the non-Horn part F\F_r that maximizes the number 
of satisfiable clauses in F\F_r . We iterate this process until the formula becomes 
renamable Horn and can be solved in polynomial time.


SelectPolarity (v):
Choose randomly the phase of the selected variable with the probability 1/2.




