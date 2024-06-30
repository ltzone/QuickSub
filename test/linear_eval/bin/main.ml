(* let main = 
  List.iter Tests.test3
  (* [10;100] *)
  (* [10;50;100;200;500;1000;2000;3000;4000;5000;6000;7000;8000;9000;10000] *)
  (* [10;100;1000] *)
  [10;100;1000;2000;5000] *)

let test_group fnames (fs:(Defs.typ -> Defs.typ -> bool) list) n =
  List.iter (fun (fname, testfun) ->
    print_string "-------------------------- ";
    print_string fname;
    print_endline " ------------------------";
    print_endline fnames;
    List.iter (testfun fs) n
  )

let main =
  (* Test normal *)
  (* let fnames = "Configurations\tLinear\tLinearTime\tLinOpt\tLinOptTime\tNominal\tNominalTime\tEqui\tEquiTime\tAmber\tAmberTime\tL17\tCompleteTime" in *)
  let fnames = "Configurations\tLinear\tLinear time\tLinOpt\tLinOpt time\tEqui\tEqui time\tAmber\tAmber time\tL17\tComplete time" in
  let fs = [
      LinearSubExt.sub; 
      LinearSubOpt.sub; 
      NominalSub2.sub; 
      EquiSub.sub; 
      AmberSub.sub; 
      CompleteSub.sub
    ] in
  let depths = 
    (* [10;100;1000;2000;5000] *)
    [10;100;1000;2000;3000;4000;5000]
    (* [5000] *)
    (* ;6000;7000;8000;9000;10000] *)
  in
  test_group fnames fs depths
    [
      ("disprove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Real", Tests.test1);
      ("prove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Nat", Tests.test2);
      ("prove: Real -> mu a. Real -> ... mu z. Real -> z <:  Nat -> mu a. Nat -> ... mu z. Nat -> z", Tests.test3);
      ("disprove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Real -> (mu b. Real -> ... -> a ,, b ,, ... ,, z)", Tests.test4);
      ("prove mu a. Real -> (mu b. Real -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z)", Tests.test5);
      ("prove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) ", Tests.test6);
      ("a mixed test", Tests.test7) ;
      ("rcd with negative variables", Tests.test_rcd);
      ("rcd with top + negative variables", Tests.test_rcd_top);
      ("rcd with positive variables", Tests.test_rcd_pos)
    ];

  (* Test records in depth and width *)
  (* let fnames = "Configurations\tLinear\tLinear time\tLinOpt\tLinOpt time\tEqui\tEqui time\tAmber\tAmber time\tL17\tComplete time" in *)
  let fnames = " Depth\tWidth\tLinear\tLinearTime\tEqui\tEquiTime\tAmber\tAmberTime\tL17\tCompleteTime" in
  let fs = [LinearSubExt.sub; 
  (* LinearSubOpt.sub;  *)
  EquiSub.sub; AmberSub.sub; 
  CompleteSub.sub] in
  let configs = [
    (* depth * width *)
    (* (1, 100);
    (1, 1000);
    (1, 2000);
    (5, 100);
    (5, 1000);
    (5, 2000);
    (10, 100);
    (10, 1000);
    (10, 2000);
    (20, 100);
    (20, 1000);
    (20, 2000);
    (50, 100);
    (50, 1000);
    (50, 2000);
    (100, 100); *)
    (100, 1000);
    (* (100, 2000);
    (200, 100);
    (200, 1000); 
    (200, 2000); *)

  ]
  in
  test_group fnames fs configs
  [
    ("rcd test2', disprove positive subtyping with a slight modification", RcdTest.test2');
    ("rcd test3, disprove negative subtyping", RcdTest.test3);
    ("rcd test2, prove positive subtyping", RcdTest.test2);
    ("rcd test1, prove negative + top", RcdTest.test1)
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

