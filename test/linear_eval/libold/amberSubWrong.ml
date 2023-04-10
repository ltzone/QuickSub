
(* Implemented for named index, with subsitution *)

open Defs;;

type env = (int * int) list

let rec wf_type (e: env) (x:typ) (i: int) : bool =
  match x with
  | Nat -> true
  | Real -> true
  | Top -> true
  | Fun (a, b) -> wf_type e a i && wf_type e b i
  | Prod (a, b) -> wf_type e a i && wf_type e b i
  | Sum (a, b) -> wf_type e a i && wf_type e b i
  | Var i -> List.mem_assoc i e || List.mem i (List.map snd e)
  | Rec (j, a) -> 
      let i' = i + 1 in
      let e' = (j, i') :: e in
      wf_type e' a i'
  | _ -> false

let rec subst_var (i: int) (x: typ) (y: typ) : typ =
  match y with
  | Nat -> Nat
  | Real -> Real
  | Top -> Top
  | Fun (a, b) -> Fun (subst_var i x a, subst_var i x b)
  | Prod (a, b) -> Prod (subst_var i x a, subst_var i x b)
  | Sum (a, b) -> Sum (subst_var i x a, subst_var i x b)
  | Var j when i = j -> x
  | Var j -> Var j
  | Rec (j, a) when i = j -> Rec (j, a)
  | Rec (j, a) ->
      Rec (j, subst_var i x a)
  | _ -> failwith "subst_var: not implemented"

let rec lift_vars n t : typ =
  match t with
  | Var i -> Var (i + n)
  | Rec (j, a) -> Rec (n + j, lift_vars n a)
  | Fun (a1, a2) -> Fun (lift_vars n a1, lift_vars n a2)
  | Prod (a1, a2) -> Prod (lift_vars n a1, lift_vars n a2)
  | Sum (a1, a2) -> Sum (lift_vars n a1, lift_vars n a2)
  | Nat -> Nat
  | Real -> Real
  | Top -> Top
  | _ -> failwith "lift_vars: not implemented"

let rec eq_type_lift m n t1 t2 =
  match (t1, t2) with
  | (Nat, Nat) -> true
  | (Real, Real) -> true
  | (Top, Top) -> true
  | (Fun (a1, a2), Fun (b1, b2))
  | (Prod (a1, a2), Prod (b1, b2))
  | (Sum (a1, a2), Sum (b1, b2)) ->
      eq_type_lift m n a1 b1 && eq_type_lift m n a2 b2
  | (Var i, Var j) -> if m then i + n = j else i = j + n
  | (Rec (j, a), Rec (k, b)) when m && j + n = k && eq_type_lift m n a b -> true
  | (Rec (j, a), Rec (k, b)) when not m && j = k + n && eq_type_lift m n a b -> true
  | _ -> false


  (* after lifting, the reflexivity comparison becomes non-trivial
     need an extra bool flag to track the lift order *)
  (* the generator needs to generate different names now
    mu. ({0} -> {1})   -> mu. ({0} -> {1})
    is no longer allowed
  *)
  (* but this is also not the case:

  e.g. 
  admitted by the eq_type_lift implementation, but should not hold
  ------------------- x
  a < d |- mu e. d <: mu b. a
  -------------------
  mu a. (mu b. a) -> mu c. nat <: mu d. (mu e. d) -> mu f. real
     

  need to decide whether there a variable is free or not, if free compare equal, if not free, compare lifted index
  
  *)


let subh_lift n (i: int) (e:env) (x:typ) (y:typ) : bool =
  let rec subh (m:bool) i e x y =
    (* m for indicating whether the right type is lifted *)
    match (x, y) with
    | (Nat, Nat) -> true
    | (Real, Real) -> true
    | (Nat, Real) -> true
    | (a, Top) -> wf_type e a i
    | (Fun (a1, a2), Fun (b1, b2)) ->
        let res1 = subh (not m) i e b1 a1 in
        let res2 = subh m i e a2 b2 in
        res1 && res2
    | (Prod (a1, a2), Prod (b1, b2)) ->
        let res1 = subh m i e a1 b1 in
        let res2 = subh m i e a2 b2 in
        res1 && res2
    | (Sum (a1, a2), Sum (b1, b2)) ->
        (* subh i e a1 b1 && subh i e a2 b2 *)
        let res1 = subh m i e a1 b1 in
        let res2 = subh m i e a2 b2 in
        res1 && res2
    | (Var i, Var j) -> List.mem (i, j) e
    | (Rec (_, _), Rec (_, _)) when eq_type_lift m n x y  -> 
      (* wf_type e (Rec (j, a)) i *)
      true
    | (Rec (j, a), Rec (k, b)) ->
        let e' = (j, k) :: e in
        subh m i e' a b
    | _, _ -> false
    in
    subh true i e x y




  
let sub (x:typ) (y:typ) : bool =
  
  let fresh_i = (numVars x) + (numVars y) in
  subh_lift (numVars x) fresh_i [] x (lift_vars (numVars x) y)