open Defs;;

type tenv = (int * typ) list

type aenv = (typ * typ) list

let rec in_aenv (dir: bool) (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : bool =
  match t1 with
  | Var i -> 
      (match List.find_opt (fun (j, _) -> i = j) te1 with
      | None -> false
      | Some (_, t1') -> in_aenv dir te1 te2 ae t1' t2)
  | _ -> 
      match t2 with
      | Var i -> 
          (match List.find_opt (fun (j, _) -> i = j) te2 with
          | None -> false
          | Some (_, t2') -> in_aenv dir te1 te2 ae t1 t2')
      | _ -> if dir then List.mem (t1, t2) ae else List.mem (t2, t1) ae


let rec subh (dir: bool) (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : aenv option =
  (* print_endline ("subh " ^ (string_of_typ t1) ^ " " ^ (string_of_typ t2)); *)
  if in_aenv dir te1 te2 ae t1 t2 then Some ae else
  let ae = (t1, t2)::ae in
  match (t1, t2) with
  | (Nat, Nat) -> Some ae
  | (Real, Real) -> Some ae
  | (Nat, Real) -> Some ae
  | (_, Top) -> Some ae
  | (Fun (a1, a2), Fun (b1, b2)) ->
      let ae1 = subh (not dir) te1 te2 ae b1 a1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh dir te1 te2 ae1' a2 b2)
  | (Prod (a1, a2), Prod (b1, b2)) ->
      let ae1 = subh dir te1 te2 ae a1 b1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh dir te1 te2 ae1' a2 b2)
  | (Sum (a1, a2), Sum (b1, b2)) ->
      let ae1 = subh dir te1 te2 ae a1 b1 in
      (match ae1 with
      | None -> None
      | Some ae1' -> subh dir te1 te2 ae1' a2 b2)
  | (Rec (i, a), _ ) ->
      subh dir ((i, t1)::te1) te2 ae a t2
  | (_, Rec (i, a)) ->
      subh dir te1 ((i, t2)::te2) ae t1 a
  | _ -> None

    

let sub (x:typ) (y:typ) : bool = 
  match subh true [] [] [] x y with
  | None -> false
  | Some _ -> true

  