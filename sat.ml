let debug = ref false
let log s = if !debug then Printf.printf s else Printf.ifprintf stdout s

(* Following Sylvain Conchon's article, we use 
 * [gamma] for valuations
 * [l] for literals
 * [delta] for formulas
 * [C] for disjunctive clauses*)

module V = Map.Make(struct type t = int let compare a b = a - b end)

type var = {
  pos: int Queue.t;
  neg: int Queue.t
}

type state =  { 
    mutable valuation: bool V.t;
    literals: var array;
    constraints: (bool option) array;
    mutable num: int;
    formula: ((int * int) option) array;
    mutable last_var: int;
    max_var: int;
  }

let h = Hashtbl.create 200
let h' : (int, int) Hashtbl.t = Hashtbl.create 200

let log_state s =
  log "State:\n";
  log "\n  num: %i\n" s.num;
  log "  last_var: %i\n" s.last_var;
  log "  max_var: %i\n" s.max_var;
  log "\n  literals:\n";
  Array.iteri (fun i var ->
    log "%i | + -\n" (i+1)) s.literals;
  log "\n formula:\n";
  Array.iteri (fun i -> function 
    | None -> log "%i :: satisfied" i
    | Some (hash,count) -> log "%i :: (%i,%i)\n" i hash count) s.formula

let state_of_list list = 
  Hashtbl.clear h;
  Hashtbl.clear h';
  let formula = Array.init (List.length list) (fun _ -> Some (0,0)) in

  let variable_counter = ref 0 in
  let list = 
    list |> List.map @@ fun disj -> disj |> List.map @@ fun (n,b) ->
      if Hashtbl.mem h n then
        (Hashtbl.find h n,b)
      else begin
        incr variable_counter;
        Hashtbl.replace h n !variable_counter;
        Hashtbl.replace h' !variable_counter n;
        log "map: %i to %i, %b\n" n !variable_counter b;
        (!variable_counter, b)
      end in

  let literals = 
    log "init literals, size %i\n" !variable_counter;
    Array.init 
    !variable_counter 
    (fun _ -> { pos = Queue.create (); neg = Queue.create () }) in

  let formula_counter = ref 0 in
  list |> List.iter (fun disj ->
    begin
      let store = List.fold_left (fun (lits,count) (n,b) ->
        log "add (%i,%b) at literals.(%i)\n" n b (n-1);
        log "..and formula.(%i) was (%i,%i)\n" !formula_counter lits count;
        (if b then begin
          Queue.push !formula_counter literals.(n-1).pos;
          (lits+n,count+1)
        end else begin
          Queue.push !formula_counter literals.(n-1).neg;
          (lits-n,count+1)
        end)
      ) (0,0) disj in
      formula.(!formula_counter) <- Some store;
      incr formula_counter
    end
  );
  let state = { literals = literals;
    valuation = V.empty;
    num = !formula_counter;
    constraints = Array.create !variable_counter None;
    formula = formula;
    last_var = 1;
    max_var = !variable_counter }
  in log_state state; state

let remove_disj s disj =
  log "remove_disj %i\n" disj;
  if s.formula.(disj) <> None then begin
    s.formula.(disj) <- None;
    s.num <- s.num - 1
  end else ()

let assign (n,b) s = s.valuation <- V.add n b s.valuation
let defined (n,b) s = V.mem n s.valuation

let neg (n,b) = (n, not b)

(* Remove all disjunctions containing l *)
let occurences (n,b) s =
  log "occurences of (%i,%b), looking at s.literals.(%i)\n" n b (n-1);
  if b
  then s.literals.(n-1).pos
  else s.literals.(n-1).neg

let remove_disj_with l s = 
  log "remove_disj_with (%i,%b)\n" (fst l) (snd l);
  (occurences l s) |> Queue.iter @@ fun occ -> remove_disj s occ

let save lit map =
  log "saving %i on stack\n" lit;
  let n,b = abs lit, lit > 0 in
  try
    if b = (V.find n map) then map else raise Exit
  with Not_found ->
    V.add n b map

(* Remove l everywhere it appears *)
let remove_lit (n,b) s map = 
  log "Remove_lit (%i,%b)\n" n b;
  let aux map occurence = 
    match map with None -> raise Exit | Some map ->
    match s.formula.(occurence) with
    | None -> Some map
    | Some (lits,count) ->
      let rest = if b then lits - n else lits + n in
      s.formula.(occurence) <- Some (rest, count-1);
      log "... in remove_lit:  (rest,%i), (new count,%i)\n" rest (count-1);
      match count-1 with
      | 0 -> raise Exit
      | 1 -> remove_disj s occurence; Some (save rest map)
      | _ -> Some map
  in 
  try Queue.fold aux (Some map) (occurences (n,b) s) with Exit -> None
  (*List.map (fun disj -> List.filter (fun l' -> l <> l') disj) delta*)

let bcp l s =
  log "bcp (%i,%b)\n" (fst l) (snd l);
  remove_disj_with l s; remove_lit (neg l) s

(* Clean maximally:
  * 1) Repeatedly propagate constraints (BCP)
  * 2) If some l has to be assumed, assume it and recurse. (ASSUME)
  *    Otherwise, stop *)
let rec clean l s =
  log "Clean (%i,%b)\n" (fst l) (snd l);
  let rec recursor l s map =
    log_state s;
    match bcp l s map with
    | None -> false
    | Some map -> assign l s; assume s map

  and assume s map =
    if V.is_empty map 
    then true 
    else let (n,b) = V.min_binding map in recursor (n,b) s (V.remove n map) 

  in recursor l s (V.empty)

let trivially_true s = s.num <= 0

let rec next_lit s =
  log "next lit, last_var: %i, max_var: %i\n" s.last_var s.max_var;
  if s.last_var <= s.max_var
  then 
    if V.mem (s.last_var) s.valuation 
    then (s.last_var <- s.last_var + 1 ; next_lit s)
    else Some (s.last_var,true)
  else
    None


(* Main solver
 * - If delta is True, return current valuation
 * - If delta is trivially unsatisfiable, backtrack (CONFLICT)
 * - Otherwise, assume a new literal and recursively solve 
 *   on a cleaned version of the resulting system (UNSAT) *)
let rec solve' s k =
  if trivially_true s then
    Some s.valuation

  else match next_lit s with
  | None -> print_endline "error: no next var"; None
  | Some l ->
    let build l s = clean l s in
    let s' = { s with formula = Array.copy s.formula } in (* TODO inefficient *)
    let k' = (fun () -> 
      log "--- backtrack\n";
      if (build (neg l) s) then
      solve' s k
      else k ()) in
    if build l s' 
    then solve' s' k'
    else k' ()

(* Initiate solving *)
let solve list = 
  match solve' (state_of_list list) (fun () -> None) with
  | None -> None
  | Some valuation -> 
      Some (List.map (fun (n,b) -> Hashtbl.find h' n, b) (V.bindings valuation))

(* Print resulting valuation when the formulas is SAT *)
let print_bindings bindings = 
  let rec aux = function
    | [] -> ()
    | (n,b)::r -> print_endline ((string_of_int n)^": "^(string_of_bool b)); aux r
  in aux bindings

let print_solve l =
  match solve l with
  | None -> print_endline "No"
  | Some bindings -> print_endline "ok"; print_bindings bindings

let run_sat string_formula = 
  let open Sudoku in
  string_formula |> formulate  |> list_of_fnc |> solve |> sat_result
