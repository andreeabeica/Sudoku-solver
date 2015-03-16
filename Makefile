all:
	ocamlbuild -lib str main.byte
	mv main.byte sudoku-solver

clean:
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f *.mli
	rm -f $(EXEC)
	rm -f $(EXEC).opt
	rm sudoku-solver
	rm dimacs.txt
	rm solution.txt