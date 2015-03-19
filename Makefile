all:
	ocamlbuild -use-ocamlfind -libs str,unix main.native
	mv main.native sudoku-solver

clean:
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f *.mli
	rm -f sudoku-solver
	rm -f dimacs.txt
	rm -f solution.txt
