all:
	ocamlbuild -use-ocamlfind -libs str,unix src/main.native
	mv main.native sudoku-solver

clean:
	rm -f *.cm[iox] *~ .*~ #*#
	rm -f *.mli
	rm -r _build
