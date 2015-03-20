let debug = ref false
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
   * the given literal is true *)
  val bcp : lit -> form -> form

  (* Find a clause with exactly one literal *)
  (* A more elegant type would be form -> lit option *)
  val get_forced_lit : form -> (lit * form) option

  (* Whether the given formula is trivially true (empty)
   * or trivially false (contains an empty disjunction *)
  val trivially_true : form -> bool
  val trivially_false : form -> bool

  (* Next undefined variable mentioned by the formula *)
  val next_var : form -> int option

  (* input/output *)
  val bindings : valu -> (int * bool) list
  val to_form : (int * bool) list list -> form
  val to_lit : int -> bool -> lit

end

module S : Solver = struct
  module ValMap = Map.Make(struct type t = int let compare a b = a - b end)

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
  let remove_lit l delta : form = 
    List.map (fun disj -> List.filter (fun l' -> l <> l') disj) delta

  let bcp l delta =
    delta |> remove_disj l |> remove_lit (neg l)

  let get_forced_lit delta =
    let rec aux acc = function
      | [] -> None
      | [l]::delta' -> Some (l, acc@delta')
      | disj::delta' -> aux (disj::acc) delta'
    in aux [] delta

  let trivially_true = function [] -> true | _ -> false

  let trivially_false = List.exists (function [] -> true | _ -> false)

  let next_var = function ((n,_)::_)::_ -> Some n | _ -> None

  let bindings = ValMap.bindings
  let to_form list = list
  let to_lit n b = (n,b)
end

(* Clean maximally:
  * 1) Repeatedly propagate constraints (BCP)
  * 2) If some l has to be assumed, assume it and recurse. (ASSUME)
  *    Otherwise, stop *)
let rec clean gamma l delta =
  delta |> S.bcp l |> assume (S.assign l gamma)

and assume gamma delta =
  match S.get_forced_lit delta with
  | Some (l, delta') -> clean gamma l delta'
  | None -> (gamma,delta)

(* Main solver
 * - If delta is True, return current valuation
 * - If delta is trivially unsatisfiable, backtrack (CONFLICT)
 * - Otherwise, assume a new literal and recursively solve 
 *   on a cleaned version of the resulting system (UNSAT) *)
let rec solve' (gamma,delta) k =
  if S.trivially_true delta then
    Some gamma

  else if S.trivially_false delta then
    k ()

  else match S.next_var delta with
  | None -> print_endline "error: no next var"; None
  | Some n ->
    let build l = clean gamma l delta in
    solve' (build (S.to_lit n true)) (fun () -> solve' (build (S.to_lit n false)) k)

(* Initiate solving *)
let solve delta = match solve' (S.empty_valuation,delta) (fun setA -> None) with
| None -> None
| Some gamma -> Some (S.bindings gamma)

(* Print resulting valuation when the formulas is SAT *)
let print_valu bindings = 
  let rec aux = function
    | [] -> ()
    | (n,b)::r -> print_endline ((string_of_int n)^": "^(string_of_bool b)); aux r
  in aux bindings

let print_solve l =
  match solve @@ S.to_form l with
  | None -> print_endline "No"
  | Some bindings -> print_endline "ok"; print_valu bindings

let run_sat string_formula = 
  let open Sudoku in
  string_formula |> formulate |> list_of_fnc |> S.to_form |> solve |> sat_result
