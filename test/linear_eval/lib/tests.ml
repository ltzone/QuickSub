open Defs;;

exception Timeout

let max_time = 2.

let test_wrap ?(print=false) (fs: (typ -> typ -> bool) list) n t1 t2  =
(if print then
  (print_string "t1 := ";
    print_typ t1;
    print_endline "";
    print_string "t2 := ";
    print_typ t2;
    print_endline "") else ());
  Printf.printf "%s\t" n;
  List.iter (fun f -> 
    let start = Unix.gettimeofday () in
    let alarm = Gc.create_alarm (fun () ->
      if Unix.gettimeofday () -. start > max_time
      then raise Timeout) in
      let res, timeout_flag = try (f t1 t2, false) with 
        Timeout -> (false, true) in
      Gc.delete_alarm alarm;
      let endt = Unix.gettimeofday () in
      if timeout_flag then
        (* Printf.printf "N/A   \tTimeout   \t" *)
        Printf.printf "%B\t%f\t" res (endt -. start)
      else
        Printf.printf "%B\t%f\t" res (endt -. start)
  ) fs;
  print_endline ""
  



let test_wrapper ?(print=false) n t1 t2  = 
  let linear_start = Unix.gettimeofday () in
  let linear_res = LinearSubExt.sub t1 t2 in
  let linear_end = Unix.gettimeofday () in
  (* let linear2_start = Unix.gettimeofday () in
  let linear2_res = LinearSubOpt.sub t1 t2 in
  let linear2_end = Unix.gettimeofday () in *)

  (* let nominal_start = Unix.gettimeofday () in
  let nominal_res = NominalSub.sub t1 t2 in
  let nominal_end = Unix.gettimeofday () in *)


  let amber_start = Unix.gettimeofday () in
  let amber_res = AmberSub.sub t1 t2 in
  let amber_end = Unix.gettimeofday () in
  let complete_start = Unix.gettimeofday () in
  let complete_res = CompleteSub.sub t1 t2 in
  let complete_end = Unix.gettimeofday () in

  let equi_start = Unix.gettimeofday () in
  let equi_res = EquiSub.sub t1 t2 in
  let equi_end = Unix.gettimeofday () in



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
  (* Printf.printf "%u\t%B\t%f\t%B\t%f\t%B\t%f\t%B\t%f\n" n linear_res (linear_end -. linear_start) linear2_res (linear2_end -. linear2_start) complete_res (complete_end -. complete_start) amber_res (amber_end -. amber_start) *)
  Printf.printf "%u\t" n;
  Printf.printf "%B\t%f\t" linear_res (linear_end -. linear_start);
  (* Printf.printf "%B\t%f\t" linear2_res (linear2_end -. linear2_start); *)
  (* Printf.printf "%B\t%f\t" nominal_res (nominal_end -. nominal_start); *)
  Printf.printf "%B\t%f\t" complete_res (complete_end -. complete_start);
  Printf.printf "%B\t%f\t" equi_res (equi_end -. equi_start);
  Printf.printf "%B\t%f\n" amber_res (amber_end -. amber_start)
  
  (* Printf.printf "%u\t%B\t%f\t%B\t%f\t%B\t%f\n" n linear_res (linear_end -. linear_start) complete_res (complete_end -. complete_start) amber_res (amber_end -. amber_start) *)

(* let string_of_int n =  *)
  (* Printf.sprintf "(  %d  )" n *)


(* disprove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Real *)
let test1 fs (n:int) = 
  let t1, t2 = deep_subtyp_gen n Nat Real in
  test_wrap fs (string_of_int n) t1 t2


(* Test2: prove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Nat *)
let test2 fs (n:int) = 
  let t1, t2 = deep_subtyp_gen n Nat Nat in
  test_wrap fs (string_of_int n) t1 t2

(* Test3: prove: Real -> mu a. Real -> ... mu z. Real -> z <:  Nat -> mu a. Nat -> ... mu z. Nat -> z  *)
let test3 fs (n:int) = 
  let t1, t2 = deep_subtyp_pos_gen n Real Nat in
  test_wrap fs (string_of_int n) t1 t2


(* Test4: disprove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Real -> (mu b. Real -> ... -> a ,, b ,, ... ,, z) 

  --- the "optimized" linear algorithm is slower, due to the set/unset operation of the imperative map 
*)
let test4 fs (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Nat Real in
  test_wrap fs (string_of_int n) t1 t2

(* Test5: prove mu a. Real -> (mu b. Real -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) *)
let test5 fs (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Real Nat in
  test_wrap fs (string_of_int n) t1 t2


(* Test6: prove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) 

because we execute the refl test first

*)
let test6 fs (n:int) = 
  let t1, t2 = deep_subtyp_pos_mul_gen n Real Real in
  test_wrap fs (string_of_int n) t1 t2


let test7 fs (n:int) = 
  let t1, t2 = composite_gen 10 (n / 10) Real Nat in
  test_wrap fs (string_of_int n) t1 t2



let test_rcd fs (n:int) = 
  (* Real ->a , a -> Real <:  Real -> a, a -> Real *)
  let t1, t2 = record_gen n Nat Real Real Real  in
  test_wrap fs (string_of_int n) t1 t2


let test_rcd_top fs (n:int) = 
  (* Real ->a , Top -> Real <:  Real -> a, a -> Real *)
  let t1, t2 = record_gen n Real Real Real Real  in
  test_wrap fs (string_of_int n) t1 t2

let test_rcd_pos fs (n:int) = 
  (* Real ->a  <:  Real -> a *)
  let t1, t2 = record_gen_pos n Real Nat   in
  test_wrap fs (string_of_int n) t1 t2
  

(* let f = LinearSubExt.subh LinearSubExt.VMap.empty LinearSubExt.Pos *)
let f x y = 
  (* let fresh_i = max (numVars x) (numVars y) in
  AmberSub.subh fresh_i [] x y *)
  CompleteSub.sub x y

(* test rcd subtyping *)
let t1 = Rec (0,(Rcd (map_of_list [("x", Nat); ("y", Nat)])))
let t2 = Rec (0,(Rcd (map_of_list [("x", Top); ("y", Nat)])))
let t3 = Rec (0,(Rcd (map_of_list [("x", Nat); ("y", Top)])))
let t4 = Rec (0,(Rcd (map_of_list [("y", Top)])))

let t5 = Rec (0,(Rcd (map_of_list [("x", Nat); ("y", Nat); ("z", Nat)])))


let t6 = Rec (0,(Rcd (map_of_list [("x", Fun (Var 0, Nat)); ("y", Nat); ("z", Nat)])))

let t7 = Rec (0,(Rcd (map_of_list [("x", Fun (Var 0, Nat)); ("z", Top); ("y", Nat)])))

let t8 = Rec (0, (Rcd (map_of_list [("x", Fun (Var 0, Nat)); ("y", Nat)])))

