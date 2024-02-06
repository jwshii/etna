From STLCProplang Require Import TypeBasedGenerator.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".
Axiom num_tests : nat. Extract Constant num_tests => "max_int".
Definition qctest_test_prop_SinglePreserve_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_SinglePreserve_runner))) ++ "}|]")).
Definition qctest_test_prop_MultiPreserve_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_MultiPreserve_runner))) ++ "}|]")).


Parameter OCamlString : Type.
Extract Constant OCamlString => "string".
Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""test_prop_SinglePreserve_runner"", qctest_test_prop_SinglePreserve_runner); (""test_prop_MultiPreserve_runner"", qctest_test_prop_MultiPreserve_runner)
  ] in
  let test = List.assoc test_name test_map in
  test ()

let () =
Sys.argv.(1) |> qctest_map

".

Extraction "TypeBasedGenerator_test_runner.ml" qctest_test_prop_SinglePreserve_runner qctest_test_prop_MultiPreserve_runner qctest_map.
