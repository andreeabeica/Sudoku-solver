(* TODOs
 * profiling (hard)
 * queue lone literals
 * copy imperative DS on UNSAT choice *)

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
  type disj (* Exposing this is not necessary *)
  type form
  type valu

  (* Negation of a literal *)
  val neg : lit -> lit

  (* What is says on the tin *)
  val empty_valuation : valu

  (* Give a truth-value to the variable contained in the literal,
   * depending on the sign of the literal *)
  val assign : lit -> valu -> valu

  (* Boolean constraints propagation under the assumption that
   * the given literal is true. BCP + ASSUME *)
  val clean : valu -> lit -> form -> (valu * form) option

  (* Find a clause with exactly one literal *)
  (* A more elegant type would be form -> lit option *)
  val get_forced_lit : form -> (lit * form) option

  (* Whether the given formula is trivially true (empty)
   * or trivially false (contains an empty disjunction *)
  val trivially_true : form -> bool
  val trivially_false : form -> bool

  (* Next undefined variable mentioned by the formula *)
  val next_var : valu -> form -> int option

  (* input/output *)
  val bindings : valu -> (int * bool) list
  val to_form : (int * bool) list list -> form
  val to_lit : int -> bool -> lit

end

module S : Solver = struct
  module ValMap = Map.Make(struct type t = int let compare a b = a - b end)
  module CMap = Map.Make(struct type t = int let compare a b = a - b end)

  type sign = bool
  type lit = int * sign
  type disj = lit list
  type form = disj list
  type valu = bool ValMap.t

  let neg l = (fst l, not (snd l))
  let empty_valuation = ValMap.empty
  let assign l gamma = ValMap.add (fst l) (snd l) gamma

  (* Remove all disjunctions containing l *)
  let remove_disj l delta : form = 
    List.filter (fun disj -> not (List.exists (fun l' -> l = l') disj)) delta

  (* Remove l everywhere it appears *)
  let remove_lit l lits delta : (form * (lit list)) option = 
    List.fold_left (fun acc disj ->
      match acc with None -> None | Some acc ->
      let r = List.filter (fun l' -> l <> l') disj in
      match r with
      | [l] -> Some (fst acc, l::(snd acc))
      | [] -> None
      | _ -> Some (r::(fst acc), snd acc)) (Some ([],lits)) delta

    (*List.map (fun disj -> List.filter (fun l' -> l <> l') disj) delta*)

  let bcp l lits delta =
    let delta' = remove_disj l delta in
    remove_lit (neg l) lits delta'

    (* Not used *)
  let get_forced_lit delta =
    let rec aux acc = function
      | [] -> None
      | [l]::delta' -> Some (l, acc@delta')
      | disj::delta' -> aux (disj::acc) delta'
    in aux [] delta

  (* Clean maximally:
    * 1) Repeatedly propagate constraints (BCP)
    * 2) If some l has to be assumed, assume it and recurse. (ASSUME)
    *    Otherwise, stop *)
  let rec clean gamma l delta =
    let rec bla gamma l lits delta = 
      match bcp l lits delta with
      | None -> None
      | Some (delta',lits') -> assume (assign l gamma) delta' lits'
    (*delta |> S.bcp l |> assume (S.assign l gamma)*)

    and assume gamma delta lits =
      match lits with
      | l::ls -> bla gamma l ls delta
      | [] -> Some (gamma, delta)

    in bla gamma l [] delta

  let trivially_true = function [] -> true | _ -> false

  let trivially_false = List.exists (function [] -> true | _ -> false)

  let next_var gamma delta = 
    let rec aux2 = function
      | [] -> None
      | (n,_)::disj -> if ValMap.mem n gamma then aux2 disj else Some n
    and aux1 = function
      | [] -> None
      | disj::delta -> 
        match aux2 disj with
        | Some n -> Some n
        | None -> aux1 delta
    in aux1 delta

  let bindings = ValMap.bindings
  let to_form list = list
  let to_lit n b = (n,b)
end

(* Main solver
 * - If delta is True, return current valuation
 * - If delta is trivially unsatisfiable, backtrack (CONFLICT)
 * - Otherwise, assume a new literal and recursively solve 
 *   on a cleaned version of the resulting system (UNSAT) *)
let rec solve' state k =
  match state with
  | None -> k ()
  | Some (gamma, delta) ->
  if S.trivially_true delta then
    Some gamma

  else match S.next_var gamma delta with
  | None -> print_endline "error: no next var"; None
  | Some n ->
    let build l = S.clean gamma l delta in
    solve' (build (S.to_lit n true)) (fun () -> solve' (build (S.to_lit n false)) k)

(* Initiate solving *)
let solve delta = solve' (Some (S.empty_valuation,delta)) (fun () -> None)

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
