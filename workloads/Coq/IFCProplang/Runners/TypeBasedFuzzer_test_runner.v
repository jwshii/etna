From IFCProplang Require Import TypeBasedFuzzer.
From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Set Warnings "-extraction-opaque-accessed,-extraction".

Axiom num_tests : nat. 
Extract Constant num_tests => "max_int".

Definition qctest_test_propLLNI := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_propLLNI))) ++ "}|]")).

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".

Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""test_propLLNI"", qctest_test_propLLNI)
  ] in
  let test = List.assoc test_name test_map in
  test ()


let () =
  Printf.printf ""Entering main of qc_exec\\n""; flush stdout;
  setup_shm_aux ();
  Sys.argv.(1) |> qctest_map ; flush stdout;
".


Extraction "TypeBasedFuzzer_test_runner.ml" sample1 runLoop qctest_test_propLLNI  qctest_map.
