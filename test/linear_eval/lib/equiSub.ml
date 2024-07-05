open Defs;;

exception Foo of string

type tenv = (int * typ) list

type aenv = (typ * typ) list

let rec in_aenv  (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : bool =
  (* print_endline (
    "    " ^ string_of_typ t1 ^ "," ^ string_of_typ t2 
  ); *)
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
            (* if dir then List.mem (t1, t2) ae else List.mem (t2, t1) ae *)
            List.mem (t1, t2) ae 

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

let rec subh (fuel : int ref) (te1 : tenv) (te2 : tenv) (ae : aenv) (t1 : typ) (t2 : typ) : aenv option =
    (* fuel := !fuel - 1; *)
    (* if !fuel = 0 then raise (Foo "Fuel exhausted"); *)
  let subh = subh fuel in


  (* print_endline ("subh [" ^ (String.concat ";" (List.map (fun (a,b) -> string_of_typ a ^ "<:" ^ string_of_typ b) ae) )
         ^ "]|-" ^ (string_of_typ t1) ^ " <: " ^ (string_of_typ t2)); *)
  (* let t1' = match t1 with
    | Var i -> (match List.find_opt (fun (j, _) -> i = j) (if dir then te1 else te2) with
      | None -> raise (Foo "Var not found")
      | Some (_, t1') -> t1')
    | _ -> t1 in
  let t2' = match t2 with
    | Var i -> (match List.find_opt (fun (j, _) -> i = j) (if dir then te2 else te1) with
      | None -> raise (Foo "Var not found")
      | Some (_, t2') -> t2')
    | _ -> t2 in  *)

    let t1' = form_type te1 t1 in
    let t2' = form_type te2 t2 in
  
    (* print_endline (" --subh [" ^ (String.concat ";" (List.map (fun (a,b) -> string_of_typ a ^ "<:" ^ string_of_typ b) ae) )
    ^ "]|-" ^ (string_of_typ t1') ^ "<:" ^ (string_of_typ t2')); *)


  if in_aenv te1 te2 ae t1' t2' then Some ae else
  let ae = (t1', t2')::ae in
  (* let new_ae_item = if dir then (t1', t2') else (t2', t1') in *)
  (* let ae = new_ae_item::ae in *)
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
      (* let new_entry = (i, t1') in
      if dir then subh dir (new_entry::te1) te2 ae a t2'
      else subh dir te1 (new_entry::te2) ae a t2' *)
  | (_, Rec (i, a)) ->
      subh  te1 ((i, t2')::te2) ae t1' a
        (* let new_entry = (i, t2') in
        if dir then subh dir te1 (new_entry::te2) ae t1' a
        else subh dir (new_entry::te1) te2 ae t1' a *)
  | Rcd fs, Rcd gs ->
      TMap.fold (fun l g prev -> 
        match prev with None -> None | Some prev ->
        if TMap.mem l fs then (subh  te1 te2 prev (TMap.find l fs) g) else None) gs (Some ae)
  (* | Var i, _ -> 
     (match List.find_opt (fun (j, _) -> i = j) (if dir then te1 else te2) with
     | None -> None
     | Some (_, t1') -> subh dir te1 te2 ae t1' t2)
  | _, Var i ->
      (match List.find_opt (fun (j, _) -> i = j) (if dir then te2 else te1) with
      | None -> None
      | Some (_, t2') -> subh dir te1 te2 ae t1 t2') *)
  | _ -> None


  
(* 
   


a ~ (mu b. b -> nat); b ~ (mu b. b -> nat) |- b -> nat <:  b -> nat
a ~ (mu b. b -> nat); b ~ (mu b. b -> nat) |- b -> nat <:  mu a. (mu b. b -> nat)
a ~ (mu b. b -> nat) |- (mu b. b -> nat) <: mu a. (mu b. b -> nat)
mu a. (mu b. b -> nat) <: mu a. (mu b. b -> nat)


*)


let sub (x:typ) (y:typ) : bool = 
  match subh (ref 10) [] [] [] x y with
  | None -> false
  | Some _ -> true

  