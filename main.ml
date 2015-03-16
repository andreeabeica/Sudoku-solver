open Format 

let istring = ref ""

let minisat = ref false

let set_string f s = f := s

let options = ["-minisat", Arg.Set minisat, "Use the minisat solver"]

let usage = "usage: sudoku-solver [option] sudokugrid"

let () = 
  Arg.parse options (set_string istring) usage;
  Sudoku.formatting !istring;
  Sudoku.run_minisat [];;
  
