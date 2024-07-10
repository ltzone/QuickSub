(** Constructors for types
  
  Type variables are represented as integers, which are assumed to be named 0, 1, etc, ...
  so for all types T passed as arguments to the subtype-testing function [sub],
  the set of type variables in T is {0 .. n} for some n, we also assume that T never 
  uses undeclared type variables, and has been alpha-converted to ensure the uniqueness
  of every declared variable

*)

module TMap = Map.Make(String)


let rec map_of_list l = 
  match l with
  | [] -> TMap.empty
  | (k,v)::t -> TMap.add k v (map_of_list t)


type typ = Nat | Real | Prod of typ * typ | Sum of typ * typ 
         | Fun of typ * typ | Rec of int * typ | Var of int
         | Top
         | Rcd of typ TMap.t


let rec numVars (t: typ) = match t with 
  | Prod (t1, t2) | Sum (t1, t2) | Fun (t1, t2) -> numVars t1 + numVars t2 
  | Rec (_, t) -> numVars t + 1
  | Rcd fs -> TMap.fold (fun _ t acc -> acc + numVars t) fs 0
  | _ -> 0


let range a b =
    List.init (b - a) ((+) a)


let rev_concat_map f xs = List.fold_right List.rev_append (List.rev_map f xs) []
(* The tail-recursive version of concat map *)


(* rename a type so that no parallel binders use the same index *)
let rec lev_typh (i: int) (env: (int * int) list) t : int * typ =
  match t with
  | Nat | Real | Top -> i, t
  | Var j -> i, Var (List.assoc j env)
  | Prod (t1, t2) -> 
      let i', t1' = lev_typh i env t1 in
      let i'', t2' = lev_typh i' env t2 in
      i'', Prod (t1', t2')
  | Sum (t1, t2) -> 
      let i', t1' = lev_typh i env t1 in
      let i'', t2' = lev_typh i' env t2 in
      i'', Sum (t1', t2')
  | Fun (t1, t2) -> 
      let i', t1' = lev_typh i env t1 in
      let i'', t2' = lev_typh i' env t2 in
      i'', Fun (t1', t2')
  | Rec (j, t) -> 
      let new_i = i + 1 in
      let i', t' = lev_typh new_i ((j, i) :: env) t in
      i', Rec (i, t')
  | Rcd fs -> 
      let i', fs' = TMap.fold (fun f t (i, fs) -> 
        let i', t' = lev_typh i env t in
        i', TMap.add f t' fs) fs (i, TMap.empty) in
      i', Rcd fs'

let lev_typ t = snd (lev_typh 0 [] t)

let rec typgenh (depth: int) (max_var: int) : typ list =
  if depth = 0 then 
      ([Nat; Top] @ (List.map (fun i -> Var i) (range 0 max_var)))
  else
    (let st1 = typgenh (depth - 1) max_var in
      let st2 = typgenh (depth - 1) (max_var + 1) in
        let st1_comb = rev_concat_map 
            (fun t1 -> rev_concat_map (fun t2 -> [
              (* Prod (t1, t2);  *)
              (* Sum (t1, t2);  *)
            Fun (t1, t2)]) st1) st1 in
        let st2_comb = rev_concat_map (fun t -> [Rec (max_var, t)]) st2 in
        List.rev_append st1_comb st2_comb
    )
    



let typgen (depth: int) = 
   List.rev_map lev_typ (typgenh depth 0)

let ascii n = String.make 1 (Char.chr (Char.code 'a' + n))

let rec string_of_typ t = match t with
  | Nat -> "nat"
  | Real -> "real"
  | Prod (t1, t2) -> "(" ^ string_of_typ t1 ^ " * " ^ string_of_typ t2 ^ ")"
  | Sum (t1, t2) -> "(" ^ string_of_typ t1 ^ " + " ^ string_of_typ t2 ^ ")"
  | Fun (t1, t2) -> "(" ^ string_of_typ t1 ^ " -> " ^ string_of_typ t2 ^ ")"
  | Rec (i, t) -> "(μ " ^ ascii i ^ ". " ^ string_of_typ t ^ ")"
  | Var i -> ascii i
  | Top -> "T"
  | Rcd fs -> "{" ^ String.concat "; " (List.map (fun (f, t) -> f ^ ": " ^ string_of_typ t)  (TMap.bindings fs)) ^ "}"

let print_typ t = print_string (string_of_typ t)



let t1 = Rec (0, (Fun (Var 0, Nat))) (* μ a. a -> nat *)
let t2 = Rec (0, (Fun (Var 0, Real))) (* μ a. a -> real *)

let t3 = Rec (0, (Fun (Real, Var 0))) (* μ a. real -> a *)
let t4 = Rec (0, (Fun (Nat, Var 0))) (* μ a. nat -> a *)

let t1_unfold = Rec (0, (Fun (Rec (1, (Fun (Var 1, Nat))), Nat))) (* μ a. (μ b. b -> nat) -> nat *)

let t3_unfold = Rec (0, (Fun (Real, Rec (1, (Fun (Real, Var 1)))))) (* μ a. real -> (μ b. real -> b) *)

let t4_unfold = Rec (0, (Fun (Nat, Rec (1, (Fun (Nat, Var 1)))))) (* μ a. nat -> (μ b. nat -> b) *)
