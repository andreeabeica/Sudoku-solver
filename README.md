# Sudoku-solver
Automated proof project - A SAT solver for Sudoku

compiling Sudoku.ml generates two files: dfnc.txt, which contains the translation of the given Sudoku grid into a DFNC formula, and dimacs.txt, which contains the formula in DIMACS format (this should be fed to the SAT solver)

for the time being, the Sudoku grid is passed explicitly as a function argument, in Sudoku.ml
