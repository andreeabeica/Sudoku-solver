open Printf
open Pervasives
open Str
(* formatting the Sudoku grids*)

 type cellule = { i : int; j : int };;
 type atome = { cellule : cellule; d : int; signe : bool };;
 type clause = atome list;;
 type fnc = clause list;;

 let debug = ref false

let grid = Array.make_matrix 9 9 0;;


(*takes a Sudoku grid in line form and formats it into a matrix*)
let rec line2grid line countline countcolumn =
 match line with
  |"" -> grid
  |line -> 
   begin
    grid.(countline).(countcolumn) <- Char.code (String.get line 0)- 48;

    match countcolumn with
    | 8 -> 
         line2grid (String.sub line 1 ((String.length line)-1)) (countline+1) 0 
    | _ -> line2grid (String.sub line 1 ((String.length line)-1))
					 countline (countcolumn+1)
   end

;;

(*pretty printing for the matrix, with 3x3 case delimitation*)
	
let rec printgrid grid countline countcolumn =
 match countline with
  | 9 -> begin printf "---------------------\n"; () end
  | _ -> begin
	 if (countline mod 3 == 0 && countcolumn == 0) 
	 then printf "---------------------\n";
	 match countcolumn with
	  | 0|3|6 -> begin 
			printf "|%d " grid.(countline).(countcolumn); 
			printgrid  grid countline (countcolumn+1) 
		     end
	  | 8 -> begin 
		    printf "%d|\n" grid.(countline).(countcolumn); 
		    printgrid  grid (countline+1) 0 
		 end
	  | _ -> begin 
		   printf "%d " grid.(countline).(countcolumn); 
		   printgrid  grid countline (countcolumn+1)
		 end
	end
;;


(*translating into CNF formulas*)


(*DEFINEDNESS CLAUSES*)

(*for one cell*)
  let rec define_cell line column compt dclause = 
   match compt with
    | 10 -> dclause
    | _ -> define_cell line column (compt+1) 
	 ( {cellule = {i=line;j=column}; d = compt; signe = true}::dclause)
  ;;

(*for the whole grid*)
  let rec define_mat line column dfnc =  
   match line with
    |9 -> dfnc
    |_ -> let dclause = define_cell line column 1 []       
          in 
           define_mat (line+((column+1)/9)) ((column+1) mod 9) (dclause ::dfnc)
				
	;;

(*UNIQUENESS CLAUSES*)

(*for one cell*)
  let rec unique_cell line column compt compt' dfnc = 
   match compt with
    | 9 -> dfnc
    | _ ->
       match compt' with
	| 9 -> unique_cell line column (compt+1) (compt+2) 
               ([{cellule = {i=line; j=column}; d = compt; signe = false};
               {cellule = {i=line; j=column}; d= compt'; signe = false}]::dfnc)
	| _ -> unique_cell line column compt (compt'+1) 
               ([{cellule = {i=line; j=column}; d = compt; signe = false};
               {cellule = {i=line; j=column}; d= compt'; signe = false}]::dfnc)
 ;;

(*for the whole grid*)

 let rec unique_mat line column dfnc =
  match line with
   | 9 -> dfnc
   | _ ->  
     let cell_dfnc = unique_cell line column 1 2 [] 
     in 
      unique_mat (line+((column+1)/9)) ((column+1) mod 9) 
                             (List.append cell_dfnc dfnc)
 ;;
	

(*VALIDITY CLAUSES*)

(*array constructors; construct arrays of indices*)

let array_sgrid x y = 
  Array.of_list [{i=x;j=y};{i=x;j=y+1};{i=x;j=y+2};{i=x+1;j=y};{i=x+1;j=y+1};
                 {i=x+1;j=y+2};{i=x+2;j=y};{i=x+2;j=y+1};{i=x+2;j=y+2}];;
	
let array_line x = 
 Array.of_list [{i=x;j=0};{i=x;j=1};{i=x;j=2};{i=x;j=3};{i=x;j=4};{i=x;j=5};
                {i=x;j=6};{i=x;j=7};{i=x;j=8}];;

let array_column y = 
 Array.of_list [{i=0;j=y};{i=1;j=y};{i=2;j=y};{i=3;j=y};{i=4;j=y};{i=5;j=y};
                {i=6;j=y};{i=7;j=y};{i=8;j=y}];;

(*validity formulas*)

(*iarray is the array holding the indices of the cells being considered: 
  array_sgrid for small grid, array_line for line and array_column for column*)

let rec valid iarray i' j' d' dfnc =
 match i' with
  |8 -> dfnc
  |_ -> 
   match j' with 
   |8 -> 
    if d'=9 
    then valid iarray (i'+1) (i'+2) 1 
    ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};
    {cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc) 
    else valid iarray i' j' (d'+1) 
    ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};
    {cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc)
			
   | _ -> match d' with
    | 9 -> 
      valid iarray i' (j'+1) 1 
      ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};
      {cellule ={i=iarray.(j').i; j= iarray.(j').j};d=d';signe=false}] :: dfnc) 
    | _ -> valid iarray i' j' (d'+1) 
      ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};
      {cellule ={i=iarray.(j').i; j= iarray.(j').j};d=d';signe=false}] :: dfnc)
	;;			


			


(*SMALL GRID*)

let valid_small_grid i j = 
  let iarray = array_sgrid i j 
  in
    valid iarray 0 1 1 [];;

let rec valid_all_small_grids i j dfnc=
 match i with
  | 9 -> dfnc
  | _ -> match j with
    | 6 -> 
       valid_all_small_grids (i+3) 0 (List.append (valid_small_grid i j) dfnc)
    | _ -> 
       valid_all_small_grids i (j+3) (List.append (valid_small_grid i j) dfnc)
	;;
				

(*LINE*)

let valid_line i = 
 let iarray = array_line i 
 in
   valid iarray 0 1 1 [];;

let rec valid_all_lines i dfnc=
 match i with
  | 9 -> dfnc
  | _ -> valid_all_lines (i+1) (List.append (valid_line i) dfnc)
;;

(*COLUMN*)

let valid_column j = 
 let iarray = array_column j 
  in
     valid iarray 0 1 1 [];;

let rec valid_all_columns j dfnc=
 match j with
  | 9 -> dfnc
  | _ -> valid_all_columns (j+1) (List.append (valid_column j) dfnc)
;;

(*formulas for filled in cases*)
let rec unique_mat line column dfnc =
 match line with
  | 9 -> dfnc
  | _ -> let cell_dfnc = unique_cell line column 1 2 [] 
         in 
          unique_mat (line+((column+1)/9)) ((column+1) mod 9) 
                     (List.append cell_dfnc dfnc)

 ;;

let rec fill_case  line column dfnc=
 match line with
  | 9 -> dfnc
  | _ -> 
    if grid.(line).(column) <> 0 
    then fill_case  (line+(column+1)/9) ((column+1) mod 9) 
       ([{cellule={i=line;j=column};d=grid.(line).(column);signe=true}]::dfnc) 
    else fill_case  (line+(column+1)/9) ((column+1) mod 9) dfnc
	;;
		
(*TODO - GET RID OF UNNECESSARY CLAUSES*)

(*print clauses in file*)

let rec recup_clause s formula =
 match s with
  | [] -> formula
  | {cellule = {i= a; j=b}; d=d'; signe = c}:: rest -> 
	recup_clause rest (String.concat "|" [formula; 
                          (String.concat " " [Pervasives.string_of_int a;
                                              Pervasives.string_of_int b;
                                              Pervasives.string_of_int d';
                                              Pervasives.string_of_bool c;])])
;;

let printclause dfnc = 
 let out = open_out "dfnc.txt" 
 in
   List.iter (fun s ->fprintf out "Clause: %s \n" (recup_clause s "")) dfnc;
   close_out out;;

(*convert to dimacs format*)

let rec dimacs_clause s formula =
 match s with
  |[] -> String.concat " " [formula;"0"]
  |{cellule={i=a;j=b};d=d';signe=c}::rest -> 
		let sign = if c=false then "-" else "" 
                in 
                    dimacs_clause rest (String.concat " " 
                    [formula; (String.concat "" [sign;
                               Pervasives.string_of_int (81*a + 9*b + d')])])
 ;;

let printdimacs dfnc =
 let out=open_out "dimacs.txt" 
 in
  List.iter (fun s -> fprintf out "%s\n" (dimacs_clause s "")) dfnc;
  close_out out
;;

let formulate string_formula =
 let _ = line2grid string_formula 0 0 
 in
   fill_case 0 0 (unique_mat 0 0 (define_mat 0 0 
                 (valid_all_columns 0 (valid_all_lines 0 
                 (valid_all_small_grids 0 0 [])))))
;;

let formatting string_formula =
  let formula = formulate string_formula in
  (if !debug then
	printgrid grid 0 0);
	printdimacs formula;;


(*turn minisat solution into Sudoku grid*)
(*todo: solve case where minisat returns unsat*)
let filetolist f = 
 try 
  let ic = open_in f 
  in
  let n = in_channel_length ic 
  in
  let s = Bytes.create n 
  in
  let _ = really_input ic s 0 n 
  in
  let s_list = Str.split (Str.regexp " ") (Str.global_replace 
                                          (Str.regexp "SAT\n") "" (s))
  in
   close_in ic;	
   s_list
 with Not_found -> printf "Something went wrong in opening the solution file! \n";[]
;;
		
	

let rec decode_var value =
   let i = if (value mod 81 <> 0)then value/81 else (value/81 -1) 
   in 
   let j = if (value - 81*i) mod 9 <> 0 
           then (value-81*i)/ 9 
           else ((value-81*i)/9-1) 
   in 
   let d = (value - 81*i - 9*j) 
   in 
      (i,j,d)
;;

let rec turn2grid solution matrix=
 match solution with
  |a1::a2::a3::a4::a5::a6::a7::a8::a9::rest ->
      let aux =[a1;a2;a3;a4;a5;a6;a7;a8;a9] 
      in 
      let value= int_of_string (List.find (fun s -> (int_of_string s) > 0) aux) 
      in 
      let i,j,d = decode_var value 
      in
      matrix.(i).(j) <- d; 
      turn2grid rest matrix
  |_ -> matrix
;;

let rec turnvalu2grid bindings matrix =
 List.iter (fun (value,b) ->
    if b then
    let i,j,d = decode_var value in
    matrix.(i).(j) <- d
    else ()) bindings;
  matrix
;;

let rec turn2str matrix=
  Array.fold_right (fun l acc ->
		(Array.fold_right (fun d acc' ->
		(string_of_int d)^acc') l "")^acc) matrix ""
;;

 (* Capture process output channels and exit code. Adapted from Rosetta Code *)
let syscall (cmd : string) : int * string =
  let ic, oc, ec = Unix.open_process_full cmd (Unix.environment ()) in
  let bufi = Buffer.create 16 in
  let bufe = Buffer.create 16 in
  (try while true do Buffer.add_channel bufi ic 1 done with End_of_file -> ());
  (try while true do Buffer.add_channel bufe ec 1 done with End_of_file -> ());
  let retcode = Unix.(match close_process_full (ic, oc, ec) with
  | WEXITED n -> n
  | WSIGNALED _ -> 0
  | WSTOPPED _ -> 0) in
  (retcode, (Buffer.contents bufi) ^ (Buffer.contents bufe))

let run_minisat f = 
  let code, ret = 
    syscall ("minisat dimacs.txt solution.txt -no-luby -rinc=1.5 -phase-saving=0 -rnd-freq=0.02") in
  match code with
  | -1 -> 
      printf "minisat not found\n"; 
      exit 1
  | 0 | 1 | 3 -> 
      print_endline ("minisat error "^(string_of_int code)^", see EXIT CODES section of relevant man page");
      exit 1
  | 10 -> 
      let grid = turn2grid (filetolist "solution.txt") (Array.make_matrix 9 9 0) in
      printf "Solution: %s\n" (turn2str grid);
      if !debug then begin
        printf "\nDebug information\n";
        printf "------------------\n";
        printgrid grid 0 0;
        printf "\nMinisat solution output in file solution.txt\n";
        printf "Minisat debug output:\n\n";
        print_endline ret
      end;
      exit 0
  | 20 ->
      printf "NoSolution\n";
      if !debug then begin
        printf "Debug information\n";
        printf "------------------\n";
        printf "Minisat debug output:\n\n";
        print_endline ret
      end;
      exit 0
  | _ -> 
      printf "unknown minisat error\n"; 
      exit 2

let list_of_fnc fnc =
  let unique = function {cellule = {i;j}; d} -> 81 * i + 9 * j + d in
  let to_list = List.map (fun c -> List.map (fun a -> (unique a, a.signe)) c)
  in to_list fnc
