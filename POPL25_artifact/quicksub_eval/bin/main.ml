open Cmdliner


module PARAM = struct
  let max_time = ref 2.0
  let depth1 = ref 1000
  let width = ref 10
  let depth2 = ref 100
end

module TestSuite = Tests.MakeTests(PARAM)

let test_table1_cmd =
  let doc = "Run test_table1" in
  let info = Cmd.info "table1" ~doc in
  let term = Term.(const TestSuite.test_table1 $ const ()) in
  Cmd.v info term

let collect_smax_cmd =
  let doc = "Run collect_smax" in
  let info = Cmd.info "smax" ~doc in
  let term = Term.(const TestSuite.collect_smax $ const ()) in
  Cmd.v info term

let test_plot1_cmd =
  let doc = "Run test_plot1" in
  let info = Cmd.info "plot1" ~doc in
  let term = Term.(const TestSuite.test_plot1 $ const ()) in
  Cmd.v info term

let test_table2_cmd =
  let doc = "Run test_table2" in
  let info = Cmd.info "table2" ~doc in
  let term = Term.(const TestSuite.test_table2 $ const ()) in
  Cmd.v info term

let test_plot2_cmd =
  let doc = "Run test_plot2" in
  let info = Cmd.info "plot2" ~doc in
  let term = Term.(const TestSuite.test_plot2 $ const ()) in
  Cmd.v info term


let default_cmd =
  let doc = "QuickSub evaluation tool" in
  let man = [
    `S Manpage.s_description;
    `P "This tool allows for running various tests with configurable parameters."
  ] in
  Cmd.info "quicksub_eval" ~doc ~man

let () =
  let cmds = [test_table1_cmd; collect_smax_cmd; test_plot1_cmd; test_table2_cmd; test_plot2_cmd] in
  let group = Cmd.group (Cmd.info "quicksub_eval") cmds in
  exit (Cmd.eval group)
