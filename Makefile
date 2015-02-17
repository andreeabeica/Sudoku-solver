all:
	ocaml Sudoku.ml

clean:
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f *.mli
	rm -f $(EXEC)
	rm -f $(EXEC).opt