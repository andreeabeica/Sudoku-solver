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
  type lits (* literal set *)
  type disj (* Exposing this is not necessary *)
  type form
  type valu
  type info

  (* Negation of a literal *)
  val neg : lit -> lit

  (* Formulas *)
  val top : form
  val conj : form -> form -> form
  val shift : lit -> form -> form
  val sing_form : lit -> lits -> form

  (* What is says on the tin *)
  val empty_valuation : valu

  (* Give a truth-value to the variable contained in the literal,
   * depending on the sign of the literal *)
  val assign : lit -> lits -> valu -> valu

  (* Boolean constraints propagation under the assumption that
   * the given literal is true *)
  val bcp : lit -> lits -> form -> form

  (* Find a clause with exactly one literal *)
  (* A more elegant type would be form -> lit option *)
  val get_forced_lit : form -> (lit * lits * form) option

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
  type info = lits * form
  type valu = (bool*lits) ValMap.t

  let neg l = (fst l, not (snd l))
  let empty_valuation = ValMap.empty
  let assign l setA gamma = ValMap.add (fst l) (snd l,setA) gamma

  let top = []
  let conj d d' = d@d'
  let sing_form l setA = [([l],setA)]

  let union = Lits.union
  let mem = Lits.mem
  let singleton = Lits.singleton
  let remove = Lits.remove

  (* Remove all disjunctions containing l *)
  let remove_disj l delta : form = 
    List.filter (fun (disj,_) -> not (List.exists (fun l' -> l = l') disj)) delta

  (* Remove l everywhere it appears *)
  let remove_lit l setB delta : form = 
    List.map (fun (disj,setC) -> 
      match List.partition (fun l' -> l' = l) disj with
      | [], _ -> (disj,setC)
      | _, disj' -> (disj', union setB setC)) delta

  let bcp l setB delta =
    delta |> remove_disj l |> remove_lit (neg l) setB

  let get_forced_lit delta =
    let rec aux acc = function
      | [] -> None
      | ([l],setA)::delta' -> Some (l, setA, acc@delta')
      | disj::delta' -> aux (disj::acc) delta'
    in aux [] delta

  let trivially_true = function [] -> true | _ -> false

  let trivially_false delta = 
    try
    Some (snd (List.find (function ([],_) -> true | _ -> false) delta))
    with Not_found -> None

  let rec shift l = function
    | [] -> []
    | (disj,setA)::delta ->
        if mem l setA then
          ((neg l)::disj, remove l setA)::(shift l delta)
        else
          (disj,setA)::(shift l delta)

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

(* Clean maximally:
  * 1) Repeatedly propagate constraints (BCP)
  * 2) If some l has to be assumed, assume it and recurse. (ASSUME)
  *    Otherwise, stop *)
let rec clean gamma l setA delta =
  delta |> S.bcp l setA |> assume (S.assign l setA gamma)

and assume gamma delta =
  match S.get_forced_lit delta with
  | Some (l, setA, delta') -> clean gamma l setA delta'
  | None -> (gamma,delta)


(* Main solver
 * - If delta is True, return current valuation
 * - If delta is trivially unsatisfiable, backtrack (CONFLICT)
 * - Otherwise, assume a new literal and recursively solve 
 *   on a cleaned version of the resulting system (UNSAT),
 *   with early failure if assuming the dual literal would
 *   never help (BJ) *)
let rec solve' (gamma,delta) k =
  if S.trivially_true delta then
    Some gamma

  else match S.trivially_false delta with
  | Some setA -> k (setA,S.top)
  | None ->

  match S.next_var gamma delta with
  | None -> print_endline "error: no next var"; None
  | Some n ->
    let lt = S.to_lit n true
    and lf = S.to_lit n false
    and build l set delta = clean gamma l set delta in
    solve' (build lt (S.singleton lt) delta)
    (fun (setA,conflicts) -> 
      if S.mem lt setA 
      then solve' (build lf (S.remove lt setA) (S.conj delta (S.shift lt conflicts)) )
        (fun (setB,conflictsB) -> 
          let conflictsB' = S.conj 
                        (S.conj (S.shift lt conflicts) (S.sing_form lf (S.remove lt setA)))
                        conflictsB
          in k (setB,conflictsB'))
      (* UNSAT *)
      else k (setA, S.shift lt conflicts) (* BJ *))

(* Initiate solving *)
let solve delta = match solve' (S.empty_valuation,delta) (fun info -> None) with
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
