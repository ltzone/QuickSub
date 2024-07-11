open Defs;;


let typ_pair_gen (depth: int) = 
  let ts = typgen depth in
  let ts' = typgen depth in
  rev_concat_map (fun t -> List.rev_map (fun t' -> (t, t')) ts') ts

let worst_case_gen (depth: int) b = 
let rec typ_genh max_var dep = 
  if dep = 0 then b else
    Rec (max_var, List.fold_left (fun acc v -> Fun (Var v, acc))
      (typ_genh (max_var + 1) (dep - 1))
      (range 0 max_var)) in
typ_genh 0 depth

(* generate [mu a. a -> mu b. b -> ... b1 <: mu a. a -> mu b. b -> ... b2]  *)
let deep_subtyp_gen (depth: int) b1 b2 = 
let rec typ_genh max_var dep base = 
  if dep = 0 then (Fun (Var (max_var-1), base)) else
    Rec (max_var, Fun (Nat, typ_genh (max_var + 1) (dep - 1) base)) in
let t1 = typ_genh 0 depth b1 in
let t2 = typ_genh 0 depth b2 in
(t1, t2)

(* generate b1 -> mu a. b1 -> mu b. b1 -> ... -> a <: b2 -> mu a. b2 -> mu b. b2 -> ... -> a *)
let deep_subtyp_pos_gen (depth: int) b1 b2 =
let rec typ_genh max_var dep fbase base = 
  if dep = 0 then Fun (base, Var 0) else
    Fun (fbase, Rec (max_var, Fun (fbase, typ_genh (max_var + 1) (dep - 1) fbase base))) in
let t1 = typ_genh 0 depth Real b1 in
let t2 = typ_genh 0 depth Nat b2 in
(t1, t2)

let deep_subtyp_pos_mul_gen (depth: int) b1 b2 =
let rec typ_genh max_var dep base cont = 
  if dep = 0 then cont else
    Rec (max_var, Fun (base, typ_genh (max_var + 1) (dep - 1) base (Sum (Var max_var, cont)))) in
let t1 = typ_genh 0 depth Nat b2 in
let t2 = typ_genh 0 depth Nat b1 in
(t1, t2)

let mk_refl f n a _ = f n a a

let rec composite_gen (width: int) (depth: int) b1 b2 =
let gen_funcs = [ mk_refl deep_subtyp_gen ; deep_subtyp_pos_gen; deep_subtyp_pos_mul_gen ] in
let gen_func1 = List.nth gen_funcs (Random.int (List.length gen_funcs)) in
if width = 0 then gen_func1 depth b1 b2 else
let (t1, t2) = gen_func1 depth b1 b2 in
let (t3, t4) = composite_gen (width - 1) depth b1 b2 in
(Prod (t1, t3), Prod (t2, t4))




let rec make_str_label (i: int) =
let remainder = i mod 26 in
let quotient = i / 26 in
if quotient = 0 then ascii remainder else
  (ascii remainder) ^ (make_str_label quotient)


let record_gen width b1_contra b1_conv b2_contra b2_conv = 
let rec helper (width: int) : (typ TMap.t * typ TMap.t) =
  if width = 0 then TMap.empty, TMap.empty else
    let f = make_str_label width in
    let fs1, fs2 = helper (width - 1) in
    (( fs1 |> TMap.add f (Fun (b1_conv, Var 0))
       |> TMap.add (f ^ "'") (Fun (Var 0, b1_contra))),
      ( fs2 |> TMap.add f (Fun (b2_conv, Var 0))
        |> TMap.add (f ^ "'") (Fun (Var 0, b2_contra)))) in
         (* (f ^ "'", Fun (Var 0, b1_contra)) :: fs1, 
      (f, Fun (b2_conv, Var 0)) ::  (f ^ "'", Fun (Var 0, b2_contra)) :: fs2) in *)
let fs1, fs2 = helper width in
(Rec (0, Rcd fs1), Rec (0, Rcd fs2))


let record_gen_top width b1_contra b1_conv b2_contra b2_conv = 
let rec helper (width: int) : (typ TMap.t * typ TMap.t) =
  if width = 0 then TMap.empty, TMap.empty else
    let f = make_str_label width in
    let fs1, fs2 = helper (width - 1) in
    (( fs1 |> TMap.add f (Fun (b1_conv, Var 0))
        |> TMap.add (f ^ "'") (Fun (Top, b1_contra))),
      ( fs2 |> TMap.add f (Fun (b2_conv, Var 0))
        |> TMap.add (f ^ "'") (Fun (Var 0, b2_contra)))) in
          (* (f ^ "'", Fun (Var 0, b1_contra)) :: fs1, 
      (f, Fun (b2_conv, Var 0)) ::  (f ^ "'", Fun (Var 0, b2_contra)) :: fs2) in *)
let fs1, fs2 = helper width in
(Rec (0, Rcd fs1), Rec (0, Rcd fs2))


let record_gen_pos width b1_conv b2_conv = 
let rec helper (width: int) : (typ TMap.t * typ TMap.t) =
  if width = 0 then TMap.empty, TMap.empty else
    let f = make_str_label width in
    let fs1, fs2 = helper (width - 1) in
    ( 
      (fs1 |> TMap.add (f ^ "'" ) (Fun (b1_conv, Var 0))),
      (fs2 |> TMap.add (f ^ "'") (Fun (b2_conv, Var 0)))
    ) in
    (* ( (f ^ "'", Fun (b1_conv, Var 0)) :: fs1, 
      (f ^ "'", Fun (b2_conv, Var 0)) :: fs2) in *)
let fs1, fs2 = helper width in
(Rec (0, Rcd fs1), Rec (0, Rcd fs2))






(* 
generate

base type + contravariant type

mu b. {
  mu a. {
    l1: base,
    l2: a -> base
    ...
  },
  l1 : base,
  l2 : b -> base
}
*)
let rcd_typ_gen1 depth width contra_base base =
  let rec aux idx dep =
    let rcd_gen = map_of_list (
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, base)) (range 0 width) @
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, Fun (Var idx, contra_base))) (range width (width + width))
      ) in
    if dep = 0 then 
      Rec (idx, Rcd rcd_gen)
    else
      Rec (idx, Rcd (TMap.add (make_str_label idx) (aux (idx + 1) (dep - 1)) rcd_gen))
  in
  aux 0 depth




(* 
generate

base type + contravariant type

mu b. {
  mu a. {
    l1: base,
    l2: Top -> base
    ...
  },
  l1 : base,
  l2 : Top -> base
}
*)
let rcd_typ_gen1_top depth width contra_base base =
  let rec aux idx dep =
    let rcd_gen = map_of_list (
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, base)) (range 0 width) @
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, Fun (Top, contra_base))) (range width (width + width))
      ) in
    if dep = 0 then 
      Rec (idx, Rcd rcd_gen)
    else
      Rec (idx, Rcd (TMap.add (make_str_label idx) (aux (idx + 1) (dep - 1)) rcd_gen))
  in
  aux 0 depth
(* 
generate

base type + covariant type

mu b. {
  mu a. {
    l1: base,
    l2: base -> a,
    ...
  },
  l1 : base,
  l2 : base -> b
}


*)
let rcd_typ_gen2 depth width conv_base base =
  let rec aux idx dep =
    let rcd_gen = map_of_list (
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, base)) (range 0 width) @
      List.map (fun i -> (make_str_label idx ^ "__" ^ make_str_label i, Fun (conv_base, Var idx))) (range width (width + width))
      ) in
    if dep = 0 then 
      Rec (idx, Rcd rcd_gen)
    else
      Rec (idx, Rcd (TMap.add (make_str_label idx ^ "_rec") (aux (idx + 1) (dep - 1)) rcd_gen))
  in
  aux 0 depth


let rcd_typ_gen2' depth width conv_base base bbase =
  (* bbase is the final small change *)
  let rec aux idx dep =
    let rcd_gen = map_of_list (
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, base)) (range 0 width) @
      List.map (fun i -> (make_str_label idx ^ "__" ^ make_str_label i, Fun (conv_base, Var idx))) (range width (width + width))
      ) in
    let rcd_gen_base = map_of_list (
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, base)) (range 0 width) @
      List.map (fun i -> (make_str_label idx ^ "__" ^ make_str_label i, Fun (conv_base, bbase))) (range width (width + width))
      ) in
    if dep = 0 then 
      Rec (idx, Rcd rcd_gen_base)
    else
      Rec (idx, Rcd (TMap.add (make_str_label idx) (aux (idx + 1) (dep - 1)) rcd_gen))
  in
  aux 0 depth




let rcdtest1_gen  config = 
  (* 
  base type + contravariant type
  mu b. {
    mu a. {
      l1: Real,
      l2: Nat -> a
      ...
    },
    l1 : Real,
    l2 : Nat -> b
  } <: 
  mu b. {
    mu a. {
      l1: Nat,
      l2: Real -> a
      ...
    },
    l1 : Nat,
    l2 : Real -> b
  }
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen2 d w Real Nat in
  let t2 = rcd_typ_gen2 d w Nat Real in
  (t1, t2)



let rcdtest2_gen config = 
  (* 
  base type + covariant type
  mu b. {
    mu a. {
      l1: Real,
      l2: a -> Nat
      ...
    },
    l1 : Real,
    l2 : b -> Nat
  } <: 
  mu b. {
    mu a. {
      l1: Real,
      l2: Top -> Nat
      ...
    },
    l1 : Real,
    l2 : Top -> Nat
  }
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen2 d w Real Nat in
  let t2 = rcd_typ_gen2 d w Real Real in
  (t1, t2)


let paper_test3_gen config =
  (* 
  base type + covariant type
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen2 d w Real Nat in
  let t2 = rcd_typ_gen2 d w Nat Real in
  (t1, t2)

let paper_test4_gen  config =
  (* 
  base type + contravariant type + top type
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen1_top d w Nat Nat in
  let t2 = rcd_typ_gen1 d w Real Real in
  (t1, t2)



let paper_test1_gen  config = 
    (* 
    base type + covariant type + small change
    mu b. {
      mu a. {
        l1: Real,
        l2: a -> Nat
        ...
      },
      l1 : Real,
      l2 : b -> Nat
    } <: 
    mu b. {
      mu a. {
        l1: Real,
        l2: Top -> Nat
        ...
      },
      l1 : Real,
      l2 : Top -> Nat
    }
    *)
    let (d, w) = config in
    let t1 = rcd_typ_gen2 d w Real Real  in
    let t2 = rcd_typ_gen2 d w Real Nat in
    (t1, t2)





let paper_test2_gen  config = 
  (* disprove: contravariant type
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen1 d w Real Nat in
  let t2 = rcd_typ_gen1 d w Real Real in
  (t1, t2)


let test1_gen (n:int) = 
    deep_subtyp_gen n Nat Real 

let test2_gen (n:int) =
    deep_subtyp_gen n Nat Nat

let test3_gen (n:int) =
    deep_subtyp_pos_gen n Real Nat

let test4_gen (n:int) =
    deep_subtyp_pos_mul_gen n Nat Real

let test7_gen (n:int) =
    deep_subtyp_pos_mul_gen n Real Nat

let test5_gen (n:int) =
    deep_subtyp_pos_mul_gen n Real Real

let test6_gen (n:int) =
    let ta, tb = composite_gen 10 (n / 10) Real Nat in
    (lev_typ ta, lev_typ tb)

let test8_gen (n:int) =
    let t1 = Fun (Real, worst_case_gen n Real) in
    let t2 = Fun (Nat, worst_case_gen n Real) in
    t1, t2
