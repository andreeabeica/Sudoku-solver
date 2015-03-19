type ('a, 'b) choice = Left of 'a | Right of 'b

(* Following Sylvain Conchon's article, we use 
 * [gamma] for valuations
 * [l] for literals
 * [delta] for formulas
 * [C] for disjunctive clauses*)

module type Solver = sig
  (* A CNF [form]ula is made of [disj]unctions containing [lit]erals with a
   * positive or negative [sign] *)
  type sign (* Exposing this is not necessary *)
  type lit
  type lits (* literal set *)
  type disj (* Exposing this is not necessary *)
  type form
  type valu

  (* Negation of a literal *)
  val neg : lit -> lit

  (* What is says on the tin *)
  val empty_valuation : valu

  (* Give a truth-value to the variable contained in the literal,
   * depending on the sign of the literal *)
  val assign : lit -> lits -> valu -> valu

  (* Boolean constraints propagation under the assumption that
   * the given literal is true *)
  (*val bcp : lit -> lits -> form -> form*)

  (* Find a clause with exactly one literal *)
  (* A more elegant type would be form -> lit option *)
  val clean: valu -> lit -> lits -> form -> ((valu * form), lits) choice
  (*val get_forced_lit : form -> (lit * lits * form) option*)

  (* Whether the given formula is trivially true (empty)
   * or trivially false (contains an empty disjunction *)
  val trivially_true : form -> bool
  val trivially_false : form -> lits option

  (* Next undefined variable mentioned by the formula *)
  val next_var : valu -> form -> int option

  (* input/output *)
  val bindings : valu -> (int * bool) list
  val to_form : (int * bool) list list -> form
  val to_lit : int -> bool -> lit

  (* literal sets *)
  val remove : lit -> lits -> lits
  val singleton : lit -> lits
  val union : lits -> lits -> lits
  val mem : lit -> lits -> bool

end

module S : Solver = struct
  module ValMap = Map.Make(struct type t = int let compare a b = a - b end)

  type sign = bool
  type lit = int * sign
  module Lits = Set.Make(struct type t = lit let compare = compare end)
  type lits = Lits.t
  type disj = lit list
  type form = (disj * lits) list
  type valu = (bool*lits) ValMap.t

  let neg l = (fst l, not (snd l))
  let empty_valuation = ValMap.empty
  let assign l setA gamma = ValMap.add (fst l) (snd l,setA) gamma
  let defined l gamma = ValMap.mem (fst l) gamma

  let union = Lits.union
  let mem = Lits.mem
  let singleton = Lits.singleton
  let remove = Lits.remove

  (* Remove all disjunctions containing l *)
  let remove_disj l delta : form = 
    List.filter (fun (disj,_) -> not (List.exists (fun l' -> l = l') disj)) delta

  (* Remove l everywhere it appears *)
  let remove_lit l setB lits delta = 
    List.fold_left (function
      | Right setA -> fun _ -> Right setA | Left (lits, form) -> function (disj,setC) ->
      match List.partition (fun l' -> l' = l) disj with
      | [], [] -> Right setC
      | _, [] -> Right (union setB setC)
      | [], [l] -> Left ((l,setC)::lits,form)
      | [], disj' -> Left (lits,(disj,setC)::form)
      | _, [l] -> Left ((l,union setB setC)::lits, form)
      | _, disj' -> Left (lits, (disj', union setB setC)::form)) 
    (Left (lits,[])) delta


  let bcp l setB lits delta =
    delta |> remove_disj l |> remove_lit (neg l) setB lits

  (* Clean maximally:
    * 1) Repeatedly propagate constraints (BCP)
    * 2) If some l has to be assumed, assume it and recurse. (ASSUME)
    *    Otherwise, stop *)
  let rec clean gamma l setA delta =

    let rec recursor gamma l lits setA delta =
      if (defined l gamma) then
        assume gamma (Left (lits, delta))
      else
        delta |> bcp l setA lits |> assume (assign l setA gamma)

    and assume gamma = function
      | Right setA -> Right setA
      | Left (lits,delta) ->
      match lits with
      | (l,setA)::ls -> recursor gamma l ls setA delta
      | [] -> Left (gamma,delta)

    in recursor gamma l [] setA delta

  let trivially_true = function [] -> true | _ -> false

  let trivially_false delta = 
    try
    Some (snd (List.find (function ([],_) -> true | _ -> false) delta))
    with Not_found -> None

  let next_var gamma delta = 
    let rec aux2 = function
      | [] -> None
      | (n,_)::disj -> if ValMap.mem n gamma then aux2 disj else Some n
    and aux1 = function
      | [] -> None
      | (disj,_)::delta -> 
        match aux2 disj with
        | Some n -> Some n
        | None -> aux1 delta
    in aux1 delta

  let bindings gamma = List.map (fun (n,(b,l)) -> (n,b)) (ValMap.bindings gamma)
  let to_form list = List.map (fun disj -> (disj,Lits.empty)) list
  let to_lit n b = (n,b)
end


(* Main solver
 * - If delta is True, return current valuation
 * - If delta is trivially unsatisfiable, backtrack (CONFLICT)
 * - Otherwise, assume a new literal and recursively solve 
 *   on a cleaned version of the resulting system (UNSAT),
 *   with early failure if assuming the dual literal would
 *   never help (BJ) *)
let rec solve' state k =
  match state with Right setA -> k setA | Left (gamma,delta) ->
  if S.trivially_true delta then
    Some gamma

  (*else match S.trivially_false delta with*)
  (*| Some setA -> k setA*)
  (*| None ->*)

  else match S.next_var gamma delta with
  | None -> print_endline "error: no next var"; None
  | Some n ->
    let lt = S.to_lit n true
    and lf = S.to_lit n false
    and build l set = S.clean gamma l set delta in
    solve' (build lt (S.singleton lt))
    (fun setA -> 
      if S.mem lt setA 
      then solve' (build lf (S.remove lt setA)) k (* UNSAT *)
      else k setA (* BJ *))

(* Initiate solving *)
let solve delta = solve' (Left (S.empty_valuation,delta)) (fun setA -> None)

(* Print resulting valuation when the formulas is SAT *)
let print_valu gamma = 
  let rec aux = function
    | [] -> ()
    | (n,b)::r -> print_endline ((string_of_int n)^": "^(string_of_bool b)); aux r
  in aux (S.bindings gamma)

let print_solve l =
  match solve @@ S.to_form l with
  | None -> print_endline "No"
  | Some gamma -> print_endline "ok"; print_valu gamma

let run_sat string_formula = 
  let open Sudoku in
  let res = 
    string_formula |> formulate |> list_of_fnc |> S.to_form |> solve
  in match res with
  | None -> print_endline "unsat"
  | Some gamma -> 
      let grid = turnvalu2grid (S.bindings gamma) (Array.make_matrix 9 9 0) in
      printgrid grid 0 0;
      print_endline (turn2str grid)

(*let _ = run_sat*)
(*"200000058010007340604000000040001060000020000020300010000000706035400090860000004"*)
