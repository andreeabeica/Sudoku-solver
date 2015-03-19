open Format 

let istring = ref ""

let minisat = ref false
let sudoku = ref false
let debug = ref false
let test1 = ref false
let test2 = ref false

let set_string f s = f := s

let options = ["-minisat", Arg.Set minisat, "Use the minisat solver"
              ;"-debug", Arg.Set debug, "Show debug information"
              ;"-sudoku", Arg.Set sudoku, "Read sudoku grid from command line"
              ;"-test1", Arg.Set test1, "Test the fnc->form translation"
              ;"-test2", Arg.Set test2, "Simple SAT tests"
              ]

let usage = "usage: sudoku-solver [options]"

let () = 
  Arg.parse options (set_string istring) usage;
  Sudoku.debug := !debug;
  Sat.debug := !debug;
  let sudoku_str = if !sudoku then
    !istring
  else input_line stdin in
  if !minisat then begin
    Sudoku.formatting sudoku_str;
    Sudoku.run_minisat []
  end else if !test1 then begin
    let open Sudoku in
    let c = {cellule={i=0;j=0};d=0;signe=true} in
    Sat.print_solve @@
    Sudoku.list_of_fnc [[{c with d=1; signe=true}
                        ;{c with d=2; signe=false}]
                       ;[{c with d=1;signe=false}]
                       ;[{c with d=1;signe=true}
                        ;{c with d=3;signe=true}]]
  end else if !test2 then begin
    Sat.print_solve [ [1,true ; 2,false] ; [1, false] ; [1,true ; 3, true] ]
  end else
    Sat.run_sat sudoku_str
