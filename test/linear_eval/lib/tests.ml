open Defs;;

let test_wrapper ?(print=false) n t1 t2  = 
  let linear_start = Unix.gettimeofday () in
  let linear_res = LinearSub.sub t1 t2 in
  let linear_end = Unix.gettimeofday () in
  let linear2_start = Unix.gettimeofday () in
  let linear2_res = LinearSubOpt.sub t1 t2 in
  let linear2_end = Unix.gettimeofday () in
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
  (* print_endline ("Linear: " ^ (string_of_bool linear_res));
  Printf.printf "Linear time: %fs\n" (linear_end -. linear_start);
  print_endline ("Complete: " ^ (string_of_bool complete_res));
  Printf.printf "Complete time: %fs\n" (complete_end -. complete_start) *)
  Printf.printf "%u\t%B\t%f\t%B\t%f\t%B\t%f\t%B\t%f\n" n linear_res (linear_end -. linear_start) linear2_res (linear2_end -. linear2_start) complete_res (complete_end -. complete_start) amber_res (amber_end -. amber_start)


(* disprove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Real *)
let test1 (n:int) = 
  let t1, t2 = deep_subtyp_gen n Nat Real in
  test_wrapper n t1 t2


(* Test2: prove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Nat *)
let test2 (n:int) = 
  let t1, t2 = deep_subtyp_gen n Nat Nat in
  test_wrapper n t1 t2

(* Test3: prove: Real -> mu a. Real -> ... mu z. Real -> z <:  Nat -> mu a. Nat -> ... mu z. Nat -> z  *)
let test3 (n:int) = 
  let t1, t2 = deep_subtyp_pos_gen n Real Nat in
  test_wrapper n t1 t2


(* Test4: disprove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Real -> (mu b. Real -> ... -> a ,, b ,, ... ,, z) 

  --- the "optimized" linear algorithm is slower, due to the set/unset operation of the imperative map 
*)
let test4 (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Nat Real in
  test_wrapper n t1 t2

(* Test5: prove mu a. Real -> (mu b. Real -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) *)
let test5 (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Real Nat in
  test_wrapper n t1 t2


(* Test6: prove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) 

because we execute the refl test first

*)
let test6 (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Real Real in
  test_wrapper n t1 t2


let test7 (n:int) = 
  let t1, t2 = composite_gen 10 (n / 10) Real Nat in
  test_wrapper n t1 t2


let f = LinearSubExt.subh LinearSubExt.VMap.empty LinearSubExt.Pos


(* test rcd subtyping *)
let t1 = Rec (0,(Rcd [("x", Nat); ("y", Nat)]))
let t2 = Rec (0,(Rcd [("x", Top); ("y", Nat)]))
let t3 = Rec (0,(Rcd [("x", Nat); ("y", Top)]))
let t4 = Rec (0,(Rcd [("y", Top)]))

let t5 = Rec (0,(Rcd [("x", Nat); ("y", Nat); ("z", Nat)]))


let t6 = Rec (0,(Rcd [("x", Fun (Var 0, Nat)); ("y", Nat); ("z", Nat)]))

let t7 = Rec (0,(Rcd [("x", Fun (Var 0, Nat)); ("z", Top); ("y", Nat)]))


