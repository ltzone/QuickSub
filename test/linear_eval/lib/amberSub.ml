
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
  | Rcd fs -> List.for_all (fun (_, t) -> wf_type e t i) fs

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
  | Rcd fs -> Rcd (List.map (fun (l, t) -> (l, subst_var i x t)) fs)

let rec subh (i: int) (e:env) (x:typ) (y:typ) : bool =
  match (x, y) with
  | (Nat, Nat) -> true
  | (Real, Real) -> true
  | (Nat, Real) -> true
  | (a, Top) -> wf_type e a i
  | (Fun (a1, a2), Fun (b1, b2)) ->
      let res1 = subh i e b1 a1 in
      let res2 = subh i e a2 b2 in
      res1 && res2
  | (Prod (a1, a2), Prod (b1, b2)) ->
      let res1 = subh i e a1 b1 in
      let res2 = subh i e a2 b2 in
      res1 && res2
  | (Sum (a1, a2), Sum (b1, b2)) ->
      (* subh i e a1 b1 && subh i e a2 b2 *)
      let res1 = subh i e a1 b1 in
      let res2 = subh i e a2 b2 in
      res1 && res2
  | (Var i, Var j) -> List.mem (i, j) e
  | (Rec (j, a), Rec (k, b)) when j = k  && a = b -> wf_type e (Rec (j, a)) i
  | (Rec (j, a), Rec (k, b)) when j = k ->
      let j' = i + 1 in
      let k' = i + 2 in
      let e' = (j', k') :: e in
      subh k' e' (subst_var j (Var j') a) (subst_var k (Var k') b)
  | Rcd fs, Rcd gs ->
      let fs = List.sort (fun (l1, _) (l2, _) -> compare l1 l2) fs in
      let gs = List.sort (fun (l1, _) (l2, _) -> compare l1 l2) gs in
      let rec subh' fs gs =
        match (fs, gs) with
        | _, [] -> true
        | ((l, f) :: fs, (l', g) :: gs) when l = l' ->
            subh i e f g && subh' fs gs
        | ( _ :: fs, gs) -> subh' fs gs
        | _, _ -> false
      in
      subh' fs gs
      (* todo: add equivalent to refl *)
  | _, _ -> false



  
let sub (x:typ) (y:typ) : bool =
  let fresh_i = max (numVars x) (numVars y) in
  subh fresh_i [] x y