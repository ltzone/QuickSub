(* let main = 
  List.iter Tests.test3 [1;10;50;100;200;500;1000;2000;3000;4000;5000;6000;7000;8000;9000;10000] *)

(* let t1, t2 = Defs.deep_subtyp_gen 2 Nat Real in
LinearSubOpt.sub t1 t2 *)


(* Test random *)

let main = 
  let tys = Defs.typ_pair_gen 4 in
  List.iter (
    fun (t1, t2) -> 
      let res1 = LinearSubOpt.sub t1 t2 in
      let res2 = LinearSub.sub t1 t2 in
      if res1 <> res2 then
        Printf.printf "Error: %s <: %s, \t optimized:%s \t expected:%s" (Defs.string_of_typ t1) (Defs.string_of_typ t2) (string_of_bool res1) (string_of_bool res2)
  ) tys

