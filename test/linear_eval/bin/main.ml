(* let main = 
  List.iter Tests.test3
  (* [10;100] *)
  (* [10;50;100;200;500;1000;2000;3000;4000;5000;6000;7000;8000;9000;10000] *)
  (* [10;100;1000] *)
  [10;100;1000;2000;5000] *)

let main =
  List.iter (fun (fname, testfun) ->
    print_string "-------------------------- ";
    print_string fname;
    print_endline " ------------------------";
    print_endline "Depth\tLinear\tLinear time\tLinOpt\tLinOpt time\tNominal\tNominal time\tEqui\tEqui time\tAmber\tAmber time\tL17\tComplete time";
    List.iter (testfun [LinearSubExt.sub; LinearSubOpt.sub; NominalSub.sub; EquiSub.sub; AmberSub.sub; CompleteSub.sub]) 
      (* [10;100;1000;2000;5000] *)
      [10;100;1000;2000;3000;4000;5000]
      (* ;6000;7000;8000;9000;10000] *)
    )
    [
      (* ("disprove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Real", Tests.test1);
      ("prove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Nat", Tests.test2);
      ("prove: Real -> mu a. Real -> ... mu z. Real -> z <:  Nat -> mu a. Nat -> ... mu z. Nat -> z", Tests.test3);
      ("disprove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Real -> (mu b. Real -> ... -> a ,, b ,, ... ,, z)", Tests.test4);
      ("prove mu a. Real -> (mu b. Real -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z)", Tests.test5);
      ("prove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) ", Tests.test6);
      ("a mixed test", Tests.test7); *)
      ("rcd with negative variables", Tests.test_rcd);
      ("rcd with top + negative variables", Tests.test_rcd_top);
      ("rcd with positive variables", Tests.test_rcd_pos)
    ]





(* Test nominal correctness *)

(* let main = 
  let tys = Defs.typ_pair_gen 2 in
  (* print_endline (string_of_int (List.length tys)); *)
  List.iteri (
    fun _ (t1, t2) -> 
      (* (if i mod 100000 = 0 then 
        (* print_endline (string_of_int i); *)
        (* (print_string (Defs.string_of_typ t1);
        print_string " <: ";
        print_endline (Defs.string_of_typ t2)) *) ()
      else ()); *)
      let res1 = LinearSub.sub t1 t2 in
      let res2 = try NominalSub.sub t1 t2  with
      | Failure e -> print_string (Defs.string_of_typ t1);
        print_string " <: ";
        print_endline (Defs.string_of_typ t2);
        raise (Failure e  )
      in
      if res1 <> res2 then
        (
        (* print_endline (string_of_int (Defs.numVars t1)); print_endline (string_of_bool (AmberSub.eq_type_lift true (Defs.numVars t1) t1 (AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        (* print_endline (Defs.string_of_typ ((AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        Printf.printf "Error: %s <: %s, \t Amber:%s \t Linear:%s\n" (Defs.string_of_typ t1) (Defs.string_of_typ t2) (string_of_bool res1) (string_of_bool res2))
  ) tys
 *)



(* Test equi correctness *)

(* let main = 
  let tys = Defs.typ_pair_gen 2 in
  (* print_endline (string_of_int (List.length tys)); *)
  List.iteri (
    fun _ (t1, t2) -> 
      (* (if i mod 100000 = 0 then 
        (* print_endline (string_of_int i); *)
        (* (print_string (Defs.string_of_typ t1);
        print_string " <: ";
        print_endline (Defs.string_of_typ t2)) *) ()
      else ()); *)
      let res1 = LinearSub.sub t1 t2 in
      let res2 = try EquiSub.sub t1 t2  with
      | Failure e -> print_string (Defs.string_of_typ t1);
        print_string " <: ";
        print_endline (Defs.string_of_typ t2);
        raise (Failure e  )
      in
      if res1 == true && res2 == false then
        (* if res1 <> res2 then *)
        (
        (* print_endline (string_of_int (Defs.numVars t1)); print_endline (string_of_bool (AmberSub.eq_type_lift true (Defs.numVars t1) t1 (AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        (* print_endline (Defs.string_of_typ ((AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        Printf.printf "Error: %s <: %s, \t Amber:%s \t Equi:%s\n" (Defs.string_of_typ t1) (Defs.string_of_typ t2) (string_of_bool res1) (string_of_bool res2))
  ) tys *)

