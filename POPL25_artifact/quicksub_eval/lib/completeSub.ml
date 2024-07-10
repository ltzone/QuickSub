open Defs

type cetyp = CENat | CEReal | CEFun of cetyp * cetyp
           | CEVar of int | CEProd of cetyp * cetyp * bool
           | CESum of cetyp * cetyp * bool
           | CERcd of (cetyp TMap.t) * bool
           | CETop


let isUninhabited (t: cetyp) (u: bool array) : bool =
  match t with
  | CEProd (_, _, b) | CESum (_, _, b) -> b
  | CERcd (_, b) -> b
  | CEVar n -> Array.get u n
  | _ -> false

let rec init (t:typ) 
             (ut: cetyp array)  (* unroll table *)
             (u: bool array) (* value-uninhabitation flags *)
             (b: bool) (* commit value-uninhabitation of previously seen recursive type or not *) =
  match t with
  | Nat -> CENat
  | Real -> CEReal
  | Fun (t1, t2) -> CEFun (init t1 ut u b, init t2 ut u b)
  | Sum (t1, t2) -> 
      let cet1 = init t1 ut u b in
      let cet2 = init t2 ut u b in
        CESum (cet1, cet2, isUninhabited cet1 u && isUninhabited cet2 u)
  | Prod (t1, t2) ->
      let cet1 = init t1 ut u b in
      let cet2 = init t2 ut u b in
        CEProd (cet1, cet2, isUninhabited cet1 u || isUninhabited cet2 u)
  | Var n -> CEVar n
  | Rec (n, t) ->
      Array.set u n true;
      Array.set u n (isUninhabited (init t ut u true) u);
      if b then () else Array.set ut n (init t ut u false);
      CEVar n
  | Top -> 
      (* failwith "the completeness algorithm does not allow Top" *)
      CETop
  | Rcd fs ->
      let fs' = TMap.map (fun t -> (init t ut u b)) fs in
        CERcd (fs', TMap.exists (fun _ t -> isUninhabited t u) fs')

let sub (t1: typ) (t2: typ) =
  let m = numVars t1 in
  let n = numVars t2 in
  let ut1 = Array.make m CENat in
  let ut2 = Array.make n CENat in
  let u1 = Array.make m false in
  let u2 = Array.make n false in
  let cet1 = init t1 ut1 u1 false in
  let cet2 = init t2 ut2 u2 false in
  let s1 = Array.make_matrix m n false in
  let s2 = Array.make_matrix n m false in
  let rec subh (cet1, ut1, u1) (cet2, ut2, u2) (s1, s2) = 
    if isUninhabited cet1 u1 (* S-bottom *)
    then true else
      if ( match cet2 with
          | CEFun (cet2', _) -> isUninhabited cet2' u2
          | _ -> false ) then true else
      match (cet1, cet2) with
      | (CENat, CENat) -> true (* S-Nat *)
      | (CEReal, CEReal) -> true (* S-Real *)
      | (CENat, CEReal) -> true (* S-Base *)
      | (_, CETop) -> true (* S-Top *)
      | (CEFun (t1, t2), CEFun (t1', t2')) -> (* S-Fun *)
          subh (t1', ut2, u2) (t1, ut1, u1)  (s2, s1) &&
          subh (t2, ut1, u1) (t2', ut2, u2) (s1, s2)
      | (CEProd (t1, t2, _), CEProd (t1', t2', _)) -> (* S-Prod *)
          subh (t1, ut1, u1) (t1', ut2, u2) (s1, s2) &&
          subh (t2, ut1, u1) (t2', ut2, u2) (s1, s2)
      | (CESum (t1, t2, _), CESum (t1', t2', _)) -> (* S-Sum *)
          subh (t1, ut1, u1) (t1', ut2, u2) (s1, s2) &&
          subh (t2, ut1, u1) (t2', ut2, u2) (s1, s2)
      | (CEVar m, CEVar n) -> (* S-Rec *)
          if s1.(m).(n) then true else
            (s1.(m).(n) <- true;
             subh (ut1.(m), ut1, u1) (ut2.(n), ut2, u2) (s1, s2))
      | (CERcd (fs1, _), CERcd (fs2, _)) -> (* S-Rcd *)
          TMap.for_all (fun g t2 -> TMap.mem g fs1 &&
                                    subh (TMap.find g fs1, ut1, u1) (t2, ut2, u2) (s1, s2))
                       fs2

      | _ -> false
  in
    subh (cet1, ut1, u1) (cet2, ut2, u2) (s1, s2)
