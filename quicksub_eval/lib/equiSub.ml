open Defs;;
(* This is the implementation of Gapeyev et al. 2002's algorithm for 
   checking equi-recursive subtyping.
*)


exception Foo of string


(* The environment for mapping variables to their true types (to delay the substitution when unfolding recursive types) *)
type tenv = (int * typ) list

(* The environment for storing subtyping assumptions *)
type aenv = (typ * typ) list


(* checking whether two types [t1] and [t2] are in the assumption context [ae], given substitution map [te1] and [te2] for [t1] and [t2] respectively  *)
let rec in_aenv  (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : bool =
  match t1 with
  | Var i -> 
      (match List.find_opt (fun (j, _) -> i = j) te1 with
      | None -> false
      | Some (_, t1') -> in_aenv  te1 te2 ae t1' t2)
  | _ -> 
      match t2 with
      | Var i -> 
          (match List.find_opt (fun (j, _) -> i = j) te2 with
          | None -> false
          | Some (_, t2') -> in_aenv te1 te2 ae t1 t2')
      | _ -> 
            List.mem (t1, t2) ae 

(* recover the true type of a variable from the substitution environment *)
let rec form_type (te:tenv) t : typ = 
    match t with
    | Var i -> (match List.find_opt (fun (j, _) -> i = j) te with
        | None -> raise (Foo "Var not found")
        | Some (_, t') ->  t')
    | Fun (a, b) -> Fun (form_type te a, form_type te b)
    | Prod (a, b) -> Prod (form_type te a, form_type te b)
    | Sum (a, b) -> Sum (form_type te a, form_type te b)
    | Rec (i, a) -> Rec (i, form_type  ((i, (Var i))::te) a)
    | Rcd fs -> Rcd (TMap.map (fun t -> form_type te t) fs)
    | _ -> t



(* The main function for checking subtyping *)
let rec subh (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : aenv option =

    let t1' = form_type te1 t1 in
    let t2' = form_type te2 t2 in


  if in_aenv te1 te2 ae t1' t2' then Some ae else
  let ae = (t1', t2')::ae in
  match (t1', t2') with
  | (Nat, Nat) -> Some ae
  | (Real, Real) -> Some ae
  | (Nat, Real) -> Some ae
  | (_, Top) -> Some ae
  | (Fun (a1, a2), Fun (b1, b2)) ->
      let ae1 = subh te2 te1 ae b1 a1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh te1 te2 ae1' a2 b2)
  | (Prod (a1, a2), Prod (b1, b2)) ->
      let ae1 = subh te1 te2 ae a1 b1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh  te1 te2 ae1' a2 b2)
  | (Sum (a1, a2), Sum (b1, b2)) ->
      let ae1 = subh  te1 te2 ae a1 b1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh  te1 te2 ae1' a2 b2)
  | (Rec (i, a), _ ) ->
      subh  ((i, t1')::te1) te2 ae a t2'
  | (_, Rec (i, a)) ->
      subh  te1 ((i, t2')::te2) ae t1' a
  | Rcd fs, Rcd gs ->
      TMap.fold (fun l g prev -> 
        match prev with None -> None | Some prev ->
        if TMap.mem l fs then (subh  te1 te2 prev (TMap.find l fs) g) else None) gs (Some ae)
  | _ -> None




let sub (x:typ) (y:typ) : bool = 
  match subh  [] [] [] x y with
  | None -> false
  | Some _ -> true

  