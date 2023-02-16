open Defs;;

let test_wrapper ?(print=false) n t1 t2  = 
  let linear_start = Unix.gettimeofday () in
  let linear_res = LinearSub.sub t1 t2 in
  let linear_end = Unix.gettimeofday () in
  let linear2_start = Unix.gettimeofday () in
  let linear2_res = LinearSubOpt.sub t1 t2 in
  let linear2_end = Unix.gettimeofday () in
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
  Printf.printf "%u\t%B\t%f\t%B\t%f\t%B\t%f\n" n linear_res (linear_end -. linear_start) linear2_res (linear2_end -. linear2_start) complete_res (complete_end -. complete_start)


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
