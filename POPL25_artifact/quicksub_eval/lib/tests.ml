open Defs
open TestGen

exception Timeout


module type PARAM = sig
  val max_time : float ref (* Timeout for each test *)
  val depth1   : int ref   (* Depth of the table 1 test *)
  val width    : int ref  (* Rcd Width of the table 2 test *)
  val depth2   : int ref  (* Depth of the table 2 test *)
end




let fnames_wo_nominal = 
  ("No.\tLinOpt\tLinOptTime\tEqui\tEquiTime\tAmber\tAmberTime\tComplete\tCompleteTime",
    [ QuickSubOpt.sub; EquiSub.sub; AmberSub.sub; CompleteSub.sub] ) 
    
let fnames_wo_equi = 
  ("No.\tLinOpt\tLinOptTime\tNominal\tNominalTime\tAmber\tAmberTime\tComplete\tCompleteTime",
    [ QuickSubOpt.sub; NominalSub2.sub; AmberSub.sub; CompleteSub.sub])
let fnames_wo_nominal_equi = 
  ("No.\tLinOpt\tLinOptTime\tAmber\tAmberTime\tComplete\tCompleteTime",
    [ QuickSubOpt.sub; AmberSub.sub; CompleteSub.sub])

let fnames_all = 
  ("No.\tLinOpt\tLinOptTime\tNominal\tNominalTime\tEqui\tEquiTime\tAmber\tAmberTime\tComplete\tCompleteTime",
    [ QuickSubOpt.sub; NominalSub2.sub; EquiSub.sub; AmberSub.sub; CompleteSub.sub] )

let fname_only_equi = 
  ("No.\tEqui\tEquiTime",
    [ EquiSub.sub] )




module MakeTests (P : PARAM) = struct

  open P;;

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
        if Unix.gettimeofday () -. start > !max_time
        then raise Timeout) in
        let res, timeout_flag = try (f t1 t2, false) with 
          Timeout -> (false, true) in
        Gc.delete_alarm alarm;
        let endt = Unix.gettimeofday () in
        if timeout_flag then
          Printf.printf "N/A   \tTimeout   \t"
          (* Printf.printf "%B\t%f\t" res (endt -. start) *)
        else
          Printf.printf "%B\t%f\t" res (endt -. start)
    ) fs;
    print_endline ""
    


  let test_group fnames (fs:(Defs.typ -> Defs.typ -> bool) list) n =
    List.iter (fun (fname, testfun) ->
      print_string "-------------------------- ";
      print_string fname;
      print_endline " ------------------------";
      print_endline fnames;
      List.iter (testfun fs) n
    )



  (* disprove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Real *)
  let test1 fs (n:int) = 
    let t1, t2 = test1_gen n in
    test_wrap fs (string_of_int n) t1 t2


  (* Test2: prove: mu a. a -> mu b. b -> .... Nat <: mu a. a -> mu b. b -> .... Nat *)
  let test2 fs (n:int) = 
    let t1, t2 = test2_gen n in
    test_wrap fs (string_of_int n) t1 t2

  (* Test3: prove: Real -> mu a. Real -> ... mu z. Real -> z <:  Nat -> mu a. Nat -> ... mu z. Nat -> z  *)
  let test3 fs (n:int) = 
    let t1, t2 = test3_gen n in
    test_wrap fs (string_of_int n) t1 t2


  (* Test4: disprove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Real -> (mu b. Real -> ... -> a ,, b ,, ... ,, z) 

    --- the "optimized" linear algorithm is slower, due to the set/unset operation of the imperative map 
  *)
  let test4 fs (n:int) = 
    let t1, t2 = test4_gen n in
    test_wrap fs (string_of_int n) t1 t2

  (* Test5: prove mu a. Real -> (mu b. Real -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) *)
  let test5 fs (n:int) = 
    let t1, t2 =  test5_gen n in
    test_wrap fs (string_of_int n) t1 t2


  (* Test6: prove mu a. Nat -> (mu b. Nat -> ... -> a ,, b) <: mu a. Nat -> (mu b. Nat -> ... -> a ,, b ,, ... ,, z) 

  because we execute the refl test first

  *)
  let test6 fs (n:int) = 
    let t1, t2 = test6_gen n in
    test_wrap fs (string_of_int n) t1 t2


  let test7 fs (n:int) = 
    let t1, t2 = test7_gen n in
    test_wrap fs (string_of_int n) t1 t2


  let test8 fs (n:int) = 
    let t1, t2 = test8_gen n in
    test_wrap fs (string_of_int n) t1 t2
    
    
  let rcd_paper_test3 fs config =
    let (d, w) = config in
    let t1, t2 = paper_test3_gen config in
    test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2

  let rcd_paper_test4 fs config =
    let (d, w) = config in
    let t1, t2 = paper_test4_gen config in
    test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2


  let rcd_paper_test1 fs config =
    let (d, w) = config in
    let t1, t2 = paper_test1_gen config in
    test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2
    
    
  let rcd_paper_test2 fs config =
    let (d, w) = config in
    let t1, t2 = paper_test2_gen config in
    test_wrap fs (Printf.sprintf "%4d\t%4d" d w) t1 t2



  let test_table1 () =
    let fnames = "No.\tLinOpt\tLinOptTime\tNominal\tNominalTime\tEqui\tEquiTime\tAmber\tAmberTime\tComplete\tCompleteTime" in
    let fs = [
      QuickSubOpt.sub; 
      NominalSub2.sub; 
      EquiSub.sub; 
      AmberSub.sub; 
      CompleteSub.sub
    ] in 
    let depth = !depth1 in
    let tests = [
      ("1", TestGen.test1_gen, depth);
      ("2", TestGen.test2_gen, depth);
      ("3", TestGen.test3_gen, depth);
      ("4", TestGen.test4_gen, depth);
      ("5", TestGen.test5_gen, depth);
      ("6", TestGen.test6_gen, depth);
      ("7", TestGen.test7_gen, depth); 
      ("8", TestGen.test8_gen, depth/10);
    ] in
    Printf.printf "depth = %d\n" depth;
    print_endline fnames;
    List.iter (fun (n, testcase, test_depth) ->
      let t1, t2 = (testcase test_depth) in
      test_wrap ~print:false fs n t1 t2)
      tests


  let collect_smax () =
    let f = QuickSubExt.sub0 ~profile:true in
    let depth = 100 in
    let tests = [
      ("1", TestGen.test1_gen);
      ("2", TestGen.test2_gen);
      ("3", TestGen.test3_gen);
      ("4", TestGen.test4_gen);
      ("5", TestGen.test5_gen);
      ("6", TestGen.test6_gen);
      ("7", TestGen.test7_gen);
      ("8", TestGen.test8_gen);
    ] in
    Printf.printf "depth = %d\n" depth;
    List.iter (fun (n, testcase) ->
      Printf.printf "Test %s\n" n;
      let t1, t2 = (testcase depth) in
      let _ = f t1 t2 in
      () ) tests




  let test_plot1 () = 
    (* let depths_1 = [200; 400; 600; 800; 1000] in
    let depths_2 = [500; 1000; 1500; 2000; 2500] in
    let depths_3 = [400; 800; 1200; 1600; 2000] in *)
    (* let depths_4 = [100; 200; 300; 400; 500] in *)
    (* let depths = [1000; 2000; 3000; 4000; 5000] in *)
    let step_depth = !depth1 / 5 in
    let depths = List.init 5 (fun i -> (i + 1) * step_depth) in
    let tests = [
      (* ("1", TestGen.test1_gen, depths, fnames_wo_nominal_equi); *)
      ("3", TestGen.test3_gen, depths, fnames_wo_nominal_equi);
      ("4", TestGen.test4_gen, depths, fnames_wo_nominal_equi);
      ("6", TestGen.test6_gen, depths, fnames_wo_nominal_equi);
      ("7", TestGen.test7_gen, depths, fnames_wo_nominal_equi);
    ] in
    List.iter (fun (testname, testcase, depths, (fnames, fs)) ->
      Printf.printf "------- Test %s ------\n" testname;
      print_endline fnames;
      List.iter ( fun depth ->
        let t1, t2 = (testcase depth) in
        test_wrap ~print:false fs (string_of_int depth) t1 t2
      ) depths) tests

  let test_table2 () =  
    let fnames = " Depth\tWidth\tQuick\tQuickTime\tEqui\tEquiTime\tAmber\tAmberTime\tComplete\tCompleteTime" in
    let fs = [
      QuickSubOpt.sub; 
      EquiSub.sub; 
      AmberSub.sub; 
      CompleteSub.sub
      ] in
    let configs = [
    (* (100, 1000); *)
    (!depth2, !width)
    ]
    in
    test_group fnames fs configs
    [
      ("rcd test1, disprove positive subtyping with a slight modification", rcd_paper_test1);
      ("rcd test2, disprove negative subtyping", rcd_paper_test2); 
      ("rcd test3, prove positive subtyping", rcd_paper_test3); 
      ("rcd test4, prove negative + top", rcd_paper_test4)
    ]



  let test_table3 () =  
    let fnames = " Depth\tWidth\tQuick\tQuickTime\tEqui\tEquiTime\tAmber\tAmberTime\tComplete\tCompleteTime" in
    let fs = [
      QuickSubOpt.sub; 
      EquiSub.sub; 
      AmberSub.sub; 
      CompleteSub.sub
      ] in
    let configs = [
    (* depth * width *)
      (1, 100);
      (1, 1000);
      (1, 2000);
      (10, 100);
      (10, 1000);
      (10, 2000);
      (100, 100);
      (100, 1000); 
      (100, 2000);
      (200, 100);
      (200, 1000);
      (200, 2000);
    ]
    in
    test_group fnames fs configs
    [
      ("rcd test2, prove positive subtyping", rcd_paper_test3);
    ]


end