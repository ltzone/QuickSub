open Defs;;

type env = int list


let rec rename i j y =
  match y with
  | Var k when k = i -> Var j
  | Var k -> Var k
  | Nat -> Nat
  | Real -> Real
  | Fun (a, b) -> Fun (rename i j a, rename i j b)
  | Prod (a, b) -> Prod (rename i j a, rename i j b)
  | Sum (a, b) -> Sum (rename i j a, rename i j b)
  | Rec (k, _) when k = i -> raise (Failure ("rename: trying to rename an binded variable"^ (string_of_int i) ^ " " ^ string_of_int j ^ " " ^ string_of_typ y ))
  | Rec (k, a) -> Rec (k, rename i j a)
  | Top -> Top
  | Rcd ls -> Rcd (TMap.map (fun a -> rename i j a) ls)


(* replace the variable i in x with a label type using j as label and the fresh variable in y *)
let rec subst_label (i: int) (x: typ) (y: typ) =
  match x with
  | Var k when k = i -> y
  | Var k -> Var k
  | Nat -> Nat
  | Real -> Real
  | Fun (a, b) -> Fun (subst_label i a y, subst_label i b y)
  | Prod (a, b) -> Prod (subst_label i a y, subst_label i b y)
  | Sum (a, b) -> Sum (subst_label i a y, subst_label i b y)
  | Rec (k, _) when k = i -> raise (Failure ( "subst_label: trying to substitute an binded variable" ^ (string_of_int i) ^ " " ^ string_of_typ x ^ " " ^ string_of_typ y ))
  | Rec (k, a) -> Rec (k, subst_label i a y)
  | Top -> Top
  | Rcd ls -> Rcd (TMap.map (fun a -> subst_label i a y) ls)


let rec subh (i: int) (e:env) (x:typ) (y:typ) : bool * int =
  match (x, y) with
  | (Nat, Nat) -> true, i
  | (Real, Real) -> true, i
  | (Nat, Real) -> true, i
  | (_, Top) -> true, i
  | (Fun (a1, a2), Fun (b1, b2)) ->
      let (b1_sub, i1) = subh i e b1 a1 in
      let (b2_sub, i2) = subh i1 e a2 b2 in
      b1_sub && b2_sub, i2
      (* subh i e b1 a1 && subh i e a2 b2 *)
  | (Prod (a1, a2), Prod (b1, b2)) ->
      let (b1_sub, i1) = subh i e a1 b1 in
      let (b2_sub, i2) = subh i1 e a2 b2 in
      b1_sub && b2_sub, i2
      (* subh i e a1 b1 && subh i e a2 b2 *)
  | (Sum (a1, a2), Sum (b1, b2)) ->
      let (b1_sub, i1) = subh i e a1 b1 in
      let (b2_sub, i2) = subh i1 e a2 b2 in
      b1_sub && b2_sub, i2
      (* subh i e a1 b1 && subh i e a2 b2 *)
  | (Var k, Var j) when k = j -> 
      true, i
  | (Rec (k, a), Rec (j, b)) when k = j -> (* TODO: alpha renaming?? or assumption? *)
      let fresh_i = i + 1 in
      let a_subst = subst_label k a (Prod (Var fresh_i, rename k fresh_i a)) in
      let b_subst = subst_label j b (Prod (Var fresh_i, rename j fresh_i b)) in
      subh fresh_i e a_subst b_subst
  | _, _ -> false, i
    


let sub (x:typ) (y:typ) : bool = 
  let x = lev_typ x in
  let y = lev_typ y in

  fst  (subh (max (numVars x) (numVars y)) [] x y)

(* 
open Defs;;
open LinearSub;;
open NominalSub;;

let test t1 t2 =
(LinearSub.sub t1 t2, NominalSub.sub t1 t2);;

*)