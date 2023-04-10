(* let main = 
  List.iter Tests.test_rcd_pos [10;50;100;200;500;1000;2000;3000;4000;5000;6000;7000;8000;9000;10000] *)

(* let t1, t2 = Defs.deep_subtyp_gen 2 Nat Real in
LinearSubOpt.sub t1 t2 *)


let main = RcdTest.test1

(* Test random *)
(* 
let main = 
  let tys = Defs.typ_pair_gen 3 in
  (* print_endline (string_of_int (List.length tys)); *)
  List.iteri (
    fun i (t1, t2) -> 
      (if i mod 100000 = 0 then 
        (* print_endline (string_of_int i); *)
        (* (print_string (Defs.string_of_typ t1);
        print_string " <: ";
        print_endline (Defs.string_of_typ t2)) *) ()
      else ());
      let res1 = LinearSubExt.sub t1 t2 in
      let res2 = LinearSubOpt.sub t1 t2 in
      if res1 <> res2 then
        (
        (* print_endline (string_of_int (Defs.numVars t1)); print_endline (string_of_bool (AmberSub.eq_type_lift true (Defs.numVars t1) t1 (AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        (* print_endline (Defs.string_of_typ ((AmberSub.lift_vars (Defs.numVars t1) t2))); *)
        Printf.printf "Error: %s <: %s, \t Amber:%s \t Linear:%s\n" (Defs.string_of_typ t1) (Defs.string_of_typ t2) (string_of_bool res1) (string_of_bool res2))
  ) tys
 *)
