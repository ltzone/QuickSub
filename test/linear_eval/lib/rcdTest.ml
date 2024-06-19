open Defs;;

let t1 = Rec (0, (Rcd (map_of_list [("a", Nat); ("b", Nat)])));;


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
      List.map (fun i -> (make_str_label idx ^ "_" ^ make_str_label i, Fun (conv_base, Var idx))) (range width (width + width))
      ) in
    if dep = 0 then 
      Rec (idx, Rcd rcd_gen)
    else
      Rec (idx, Rcd (TMap.add (make_str_label idx) (aux (idx + 1) (dep - 1)) rcd_gen))
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



let test_wrapper ?(print=false) n t1 t2  = 
  let linear_start = Unix.gettimeofday () in
  let linear_res = LinearSubExt.sub t1 t2 in
  let linear_end = Unix.gettimeofday () in
  let linear_opt_start = Unix.gettimeofday () in
  let linear_opt_res = LinearSubOpt.sub t1 t2 in
  let linear_opt_end = Unix.gettimeofday () in
  let amber_start = Unix.gettimeofday () in
  let amber_res = AmberSub.sub t1 t2 in
  let amber_end = Unix.gettimeofday () in
  let complete_start = Unix.gettimeofday () in
  let complete_res = CompleteSub.sub t1 t2 in
  let complete_end = Unix.gettimeofday () in
  (if print then
    (print_string "t1 := ";
      print_typ t1;
      print_endline "";
      print_string "t2 := ";
      print_typ t2;
      print_endline "") else ());
  Printf.printf "%s\t%B\t%f\t%B\t%f\t%B\t%f\t%B\t%f\n" n 
    linear_res (linear_end -. linear_start) 
    linear_opt_res (linear_opt_end -. linear_opt_start)
    complete_res (complete_end -. complete_start)
    amber_res (amber_end -. amber_start)

(* successful config *)
(* let test1 () =
  let depth = [1; 2; 4; 6; 8; 10; 20; 30] in
  let width = [100; 200; 500; 1000; 2000; 3000; 4000] in
  List.iter (fun d ->
    List.iter (fun w ->
    let t1 = rcd_typ_gen2 d w Real Nat in
    let t2 = rcd_typ_gen2 d w Nat Real in
    test_wrapper (Printf.sprintf "rcd_typ_gen2 %d\t%d" d w) t1 t2
  ) width) depth


(* failed config *)
let test2 () =
  let depth = [1; 2; 4; 6; 8; 10; 20; 30] in
  let width = [100; 200; 500; 1000; 2000; 3000; 4000] in
  List.iter (fun d ->
    List.iter (fun w ->
    let t1 = rcd_typ_gen2 d w Nat Nat in
    let t2 = rcd_typ_gen2 d w Real Real in
    test_wrapper (Printf.sprintf "rcd_typ_gen2 %d\t%d" d w) t1 t2
  ) width) depth *)



let test1 fs config = 
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
  Tests.test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2
  

let test2 fs config = 
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
  Tests.test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2



let test2' fs config = 
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
    let t1 = rcd_typ_gen2' d w Real Nat Real in
    let t2 = rcd_typ_gen2' d w Real Real Nat in
    Tests.test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2
  
  




let test3 fs config = 
  (* disprove: contravariant type
  *)
  let (d, w) = config in
  let t1 = rcd_typ_gen1 d w Real Nat in
  let t2 = rcd_typ_gen1 d w Real Real in
  Tests.test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2