open Defs;;

(* This is the QuickSub implementation with support for record types.
   We use functional sets to represent the set of equality variable set
*)


type mode = Pos | Neg


type cmp = Eq | Lt 

let flip_mode (m: mode) = 
  match m with
  | Pos -> Neg
  | Neg -> Pos


module VSet = Set.Make (Int)

module VMap = Map.Make (Int)

type env = mode VMap.t

let is_empty = VSet.is_empty

let compose_cmp (c1, l1) (c2, l2) =
  match (c1, c2) with
  | (Eq, Eq) -> Some Eq
  | (Eq, Lt) -> if is_empty l1 then Some Lt else None
  | (Lt, Eq) -> if is_empty l2 then Some Lt else None
  | (Lt, Lt) -> Some Lt

let rec fv (t:typ) =
  match t with
  | Nat -> VSet.empty
  | Real -> VSet.empty
  | Fun (a, b) -> VSet.union (fv a) (fv b)
  | Prod (a, b) -> VSet.union (fv a) (fv b)
  | Sum (a, b) -> VSet.union (fv a) (fv b)
  | Var i -> VSet.singleton i
  | Rec (i, a) -> VSet.remove i (fv a)
  | Top -> VSet.empty
  | Rcd fs -> TMap.fold (fun _ t s -> VSet.union s (fv t)) fs VSet.empty



let rec subh  (evs_cnt: int ref) (e:env) (m:mode) (x:typ) (y:typ) : (cmp * VSet.t) option =
  let subh e m x y = 
      (let res = subh evs_cnt e m x y in
      (match res with
      | Some (Eq, evs_res) -> evs_cnt := max (!evs_cnt) (VSet.cardinal evs_res)
      | _ -> ());
      res)
  in
  (* update the subh function so that it can collect the |S| data in the run *)
  
  match (x, y) with
  | (Nat, Nat) -> Some (Eq, VSet.empty)
  | (Real, Real) -> Some (Eq, VSet.empty)
  | (Nat, Real) -> Some (Lt, VSet.empty)
  | (a, Top) -> if a != Top then Some (Lt, VSet.empty) else Some (Eq, VSet.empty)
  | (Fun (a1, a2), Fun (b1, b2)) ->
    Option.bind (subh e (flip_mode m) b1 a1) (fun (c1, l1) ->
      Option.bind (subh e m a2 b2) (fun (c2, l2) ->
        match compose_cmp (c1, l1) (c2, l2) with
        | Some c -> Some (c, VSet.union l1 l2)
        | None -> None))
  | (Prod (a1, a2), Prod (b1, b2)) ->
    Option.bind (subh e m a1 b1) (fun (c1, l1) ->
      Option.bind (subh e m a2 b2) (fun (c2, l2) ->
        match compose_cmp (c1, l1) (c2, l2) with
        | Some c -> Some (c, VSet.union l1 l2)
        | None -> None))
  | (Sum (a1, a2), Sum (b1, b2)) ->
    Option.bind (subh e m a1 b1) (fun (c1, l1) ->
      Option.bind (subh e m a2 b2) (fun (c2, l2) ->
        match compose_cmp (c1, l1) (c2, l2) with
        | Some c -> Some (c, VSet.union l1 l2)
        | None -> None))
  | (Var i, Var j) when i = j -> 
      (let vbind = VMap.find_opt i e in
      match vbind with
      | Some v -> if v = m then Some (Eq, VSet.empty) else Some (Eq, VSet.singleton i)
      | None -> None)
  | (Rec (i, a), Rec (j, b)) when i = j ->
      Option.bind (subh (VMap.add i m e) m a b) (fun (c, l) ->
        match c with
        | Lt -> if VSet.mem i l then None else Some (Lt, VSet.remove i l)
        | Eq -> if VSet.mem i l then Some (Eq, VSet.remove i (VSet.union (fv a) l)) else Some (Eq, l))
  


  | (Rcd fs, Rcd gs) ->
    (* check if the keys in fs are are strict subset of gs, if so the subtyping fails *)
      if TMap.exists (fun g _ -> not (TMap.mem g fs)) gs then None
      else
        (* iterate on elements of fs *)
      TMap.fold (fun f t1 prev_res ->
        Option.bind prev_res @@
        fun (c_prev, evs_prev) ->
          match TMap.find_opt f gs with
          | None -> 
            (* if there are some missing fields in gs, then the result should be at least Lt (or None) *)
              if is_empty evs_prev then Some (Lt,  VSet.empty) else None
            (* Some (Lt, VSet.empty) *)
          | Some t2 ->
            Option.bind (subh e m t1 t2) @@
            fun (c_cur, evs_cur) ->
              match compose_cmp (c_cur, evs_cur) (c_prev, evs_prev) with
              | Some c -> Some (c, VSet.union evs_cur evs_prev)
              | None -> None
      ) fs (Some (Eq, VSet.empty))



  | _, _ -> None
    
let sub0 ?(profile = false) (x:typ) (y:typ) : bool =
  (* if profile then *)
    let evs_cnt = ref 0 in
    let res = match subh evs_cnt VMap.empty Pos x y with
    | Some _ -> true
    | _ -> false in 
    if profile then
    (Printf.printf "Number of existential variables: %d\n" !evs_cnt;res)
    else res

let sub x y = sub0 ~profile:false x y