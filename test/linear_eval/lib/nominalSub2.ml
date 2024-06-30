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
let rec subst_label (p: bool) (i: int) (x: typ) (y: typ) =
  match x with
  | Var k when k = i && not p -> y
  | Var k -> Var k
  | Nat -> Nat
  | Real -> Real
  | Fun (a, b) -> Fun (subst_label (not p) i a y, subst_label p i b y)
  | Prod (a, b) -> Prod (subst_label p i a y, subst_label p i b y)
  | Sum (a, b) -> Sum (subst_label p i a y, subst_label p i b y)
  | Rec (k, _) when k = i -> raise (Failure ( "subst_label: trying to substitute an binded variable" ^ (string_of_int i) ^ " " ^ string_of_typ x ^ " " ^ string_of_typ y ))
  | Rec (k, a) -> Rec (k, subst_label p i a y)
  | Top -> Top
  | Rcd ls -> Rcd (TMap.map (fun a -> subst_label p i a y) ls)

let rec lift_typ (ofs: int) (max_idx: int) (x: typ) : typ * int =
  (* return the lifted type and the maximal index after updates *)
  match x with
  | Var i -> Var (i + ofs), max max_idx (i + ofs)
  | Nat -> Nat, max_idx
  | Real -> Real, max_idx
  | Fun (a, b) ->
      let a', max_idx' = lift_typ ofs max_idx a in
      let b', max_idx'' = lift_typ ofs max_idx' b in
      Fun (a', b'), max_idx''
  | Prod (a, b) ->
      let a', max_idx' = lift_typ ofs max_idx a in
      let b', max_idx'' = lift_typ ofs max_idx' b in
      Prod (a', b'), max_idx''
  | Sum (a, b) ->
      let a', max_idx' = lift_typ ofs max_idx a in
      let b', max_idx'' = lift_typ ofs max_idx' b in
      Sum (a', b'), max_idx''
  | Rec (k, a) ->
      let a', max_idx' = lift_typ ofs max_idx a in
      Rec (k + ofs, a'), max_idx'
  | Top -> Top, max_idx
  | Rcd ls ->
      let ls', max_idx' = TMap.fold (fun k a (acc, max_idx) ->
        let a', max_idx' = lift_typ ofs max_idx a in
        TMap.add k a' acc, max max_idx max_idx'
      ) ls (TMap.empty, max_idx) in
      Rcd ls', max_idx'



let rec subh (i: int) (e:env) (x:typ) (y:typ) : bool * int =
  (* print_endline ("subh: " ^ string_of_typ x ^ " " ^ string_of_typ y); *)
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
  | (Rec (k, a), Rec (j, b))  ->
      (* when k = j ->  *)
        (* TODO: alpha renaming?? or assumption? *)
      let fresh_i = i + 1 in
      let (a_lift, i1) = lift_typ i fresh_i (rename k fresh_i a) in
      let (b_lift, i2) = lift_typ i i1 (rename j fresh_i b) in
      let fresh_i' = i2 + 1 in
      let a_subst = subst_label true k a (Prod (Var fresh_i', a_lift)) in
      let b_subst = subst_label true j b (Prod (Var fresh_i', b_lift)) in
      subh fresh_i e a_subst b_subst
  | Rcd fs, Rcd gs ->
      TMap.for_all (fun l g -> TMap.mem l fs && fst (subh i e (TMap.find l fs) g)) gs, i
       (* TOFIX: the i should be accummulated  *)
  | _, _ -> false, i
    


let sub (x:typ) (y:typ) : bool = 
  (* let x = lev_typ x in
  let y = lev_typ y in *)

  fst  (subh (max (numVars x) (numVars y)) [] x y)

(* 
open Defs;;
open LinearSub;;
open NominalSub;;

let test t1 t2 =
(LinearSub.sub t1 t2, NominalSub.sub t1 t2);;

*)