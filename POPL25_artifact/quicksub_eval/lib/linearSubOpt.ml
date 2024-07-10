open Defs;;

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

let compose_cmp (c1, is_empty1) (c2, is_empty2) =
  match (c1, c2) with
  | (Eq, Eq) -> Some Eq
  | (Eq, Lt) -> if is_empty1 then Some Lt else None
  | (Lt, Eq) -> if is_empty2 then Some Lt else None
  | (Lt, Lt) -> Some Lt


let rec subh (evs: bool Array.t) (fvt: bool Array.t) (e:env) (m:mode) (x:typ) (y:typ) : (cmp * bool) option =
  match (x, y) with
  | (Nat, Nat) -> Some (Eq, true)
  | (Real, Real) -> Some (Eq, true)
  | (Nat, Real) -> Some (Lt, true)
  | (a, Top) -> if a = Top then Some (Eq, true) else Some (Lt, true)
  | (Fun (a1, a2), Fun (b1, b2)) ->
    Option.bind (subh evs fvt e (flip_mode m) b1 a1) (fun (c1, is_empty1) ->
      Option.bind (subh evs fvt e m a2 b2) (fun (c2, is_empty2) ->
        match compose_cmp (c1, is_empty1) (c2, is_empty2) with
        | Some c -> Some (c, is_empty1 && is_empty2)
        | None -> None))
  | (Prod (a1, a2), Prod (b1, b2)) ->
    Option.bind (subh evs fvt e m a1 b1) (fun (c1, is_empty1) ->
      Option.bind (subh evs fvt e m a2 b2) (fun (c2, is_empty2) ->
        match compose_cmp (c1, is_empty1) (c2, is_empty2) with
        | Some c -> Some (c, is_empty1 && is_empty2)
        | None -> None))
  | (Sum (a1, a2), Sum (b1, b2)) ->
    Option.bind (subh evs fvt e m a1 b1) (fun (c1, is_empty1) ->
      Option.bind (subh evs fvt e m a2 b2) (fun (c2, is_empty2) ->
        match compose_cmp (c1, is_empty1) (c2, is_empty2) with
        | Some c -> Some (c, is_empty1 && is_empty2)
        | None -> None))
  | (Var i, Var j) when i = j -> 
      (let vbind = VMap.find_opt i e in
       let res = 
          match vbind with
          | Some v -> if v = m then Some (Eq, true) else (Array.set evs i true; Some (Eq, false))
          | None -> None in
        fvt.(i) <- true; res)
  | (Rec (i, a), Rec (j, b)) when i = j -> (* TODO: alpha renaming?? or assumption? *)
      let res = 
        Option.bind (subh evs fvt (VMap.add i m e) m a b) (fun (c, is_emptyl) ->
          match c with
          | Lt -> if evs.(i) then None else Some (Lt, is_emptyl)
          | Eq -> if evs.(i) then (
              Array.iteri (fun n j -> if j then evs.(n) <- true else ()) fvt;
              evs.(i) <- false;  
              Some (Eq, Array.for_all ((=) false) evs)) else Some (Eq, is_emptyl))
      in
        fvt.(i) <- false;
        res
  | (Rcd fs, Rcd gs) ->
      if TMap.exists (fun g _ -> not (TMap.mem g fs)) gs then None
      else
        (* iterate on elements of fs *)
      TMap.fold (fun f t1 prev_res ->
        Option.bind prev_res @@
        fun (c_prev, is_empty_prev) ->
          match TMap.find_opt f gs with
          | None -> 
            (* if there are some missing fields in gs, then the result should be at least Lt (or None) *)
              if is_empty_prev then Some (Lt, true) else None
          | Some t2 ->
            Option.bind (subh evs fvt e m t1 t2) @@
            fun (c_cur, is_empty_cur) ->
                match compose_cmp (c_prev, is_empty_prev) (c_cur, is_empty_cur) with
                | Some c -> Some (c, is_empty_prev && is_empty_cur)
                | None -> None)
           fs (Some (Eq, true))

  

  | _, _ -> None



  
let sub (x:typ) (y:typ) : bool =
  let m = numVars x in
  let n = numVars y in
  let var_num = max m n in
  let fvt = Array.make var_num false in
  let evs = Array.make var_num false in
  let res = subh evs fvt VMap.empty Pos x y in
  match res with
  | Some _ -> true
  | _ -> false