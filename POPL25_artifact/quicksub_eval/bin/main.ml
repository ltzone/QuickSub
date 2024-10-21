open Cmdliner
(* This is the command line interface for the evaluation experiments

   Detailed description of the experiments can be found in the README.md file

   You can also run `dune exec quicksub_eval -- --help` to see the available options

*)


module PARAM = struct
  let max_time = ref 2.0
  let depth1 = ref 1000
  let width = ref 10
  let depth2 = ref 100
end

module TestSuite = Tests.MakeTests(PARAM)


let set_max_time t =
  PARAM.max_time := t

let set_depth1 d =
  PARAM.depth1 := d

let set_width w =
  PARAM.width := w

let set_depth2 d =
  PARAM.depth2 := d

let max_time_arg =
  let doc = "Maximum time in seconds." in
  Arg.(value & opt float !PARAM.max_time & info ["max-time"] ~docv:"MAX_TIME" ~doc)

let depth1_arg =
  let doc = "Depth parameter 1." in
  Arg.(value & opt int !PARAM.depth1 & info ["depth1"] ~docv:"DEPTH1" ~doc)

let width_arg =
  let doc = "Width parameter." in
  Arg.(value & opt int !PARAM.width & info ["width"] ~docv:"WIDTH" ~doc)

let depth2_arg =
  let doc = "Depth parameter 2." in
  Arg.(value & opt int !PARAM.depth2 & info ["depth2"] ~docv:"DEPTH2" ~doc)

let set_params = Term.(const (fun t d1 w d2 () ->
  set_max_time t;
  set_depth1 d1;
  set_width w;
  set_depth2 d2
) $ max_time_arg $ depth1_arg $ width_arg $ depth2_arg $ const ())

let test_table1_cmd =
  let doc = "Run tests for the first table" in
  let info = Cmd.info "table1" ~doc in
  let term = Term.(const (fun _ -> TestSuite.test_table1 ()) $ set_params) in
  Cmd.v info term
  

let collect_smax_cmd =
  let doc = "Collect |S| for the first table " in
  let info = Cmd.info "smax" ~doc in
  let term = Term.(const (fun _ -> TestSuite.collect_smax ()) $ set_params) in
  Cmd.v info term

let run_equi_cmd = 
  let doc = "Run tests for the EquiSub algorithm" in
  let info = Cmd.info "equi" ~doc in
  let term = Term.(const (fun _ -> TestSuite.test_equi ()) $ set_params) in
  Cmd.v info term

let test_plot1_cmd =
  let doc = "Run tests for the first plot" in
  let info = Cmd.info "plot1" ~doc in
  let term = Term.(const (fun _ -> TestSuite.test_plot1 ()) $ set_params) in
  Cmd.v info term

let test_table2_cmd =
  let doc = "Run tests for the second table - various patterns of record subtyping" in
  let info = Cmd.info "table2" ~doc in
  (* let term = Term.(const TestSuite.test_table2 $ const ()) in *)
  let term = Term.(const (fun _ -> TestSuite.test_table2 ()) $ set_params) in
  Cmd.v info term

let test_table3_cmd =
  let doc = "Run tests for the third table - records with different depths and widths" in
  let info = Cmd.info "table3" ~doc in
  (* let term = Term.(const TestSuite.test_plot2 $ const ()) in *)
  let term = Term.(const (fun _ -> TestSuite.test_table3 ()) $ set_params) in
  Cmd.v info term


let () =
  let cmds = [test_table1_cmd; collect_smax_cmd; test_plot1_cmd; test_table2_cmd; test_table3_cmd; run_equi_cmd] in

  (* set the command line argument inputs *)

  let group = Cmd.group ~default:set_params (Cmd.info "quicksub_eval") cmds in
  exit (Cmd.eval group)
