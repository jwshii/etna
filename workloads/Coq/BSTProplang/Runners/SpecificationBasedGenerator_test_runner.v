From BSTProplang Require Import SpecificationBasedGenerator.
From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".
Axiom num_tests : nat. Extract Constant num_tests => "max_int".
Definition qctest_test_prop_InsertValid_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertValid_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteValid_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteValid_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionValid_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionValid_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertPost_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertPost_runner))) ++ "}|]")).
Definition qctest_test_prop_DeletePost_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeletePost_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionPost_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionPost_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertModel_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertModel_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteModel_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteModel_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionModel_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionModel_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertInsert_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertDelete_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertDelete_runner))) ++ "}|]")).
Definition qctest_test_prop_InsertUnion_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_InsertUnion_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteInsert_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteDelete_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteDelete_runner))) ++ "}|]")).
Definition qctest_test_prop_DeleteUnion_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_DeleteUnion_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionDeleteInsert_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionDeleteInsert_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionUnionIdem_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionUnionIdem_runner))) ++ "}|]")).
Definition qctest_test_prop_UnionUnionAssoc_runner := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionUnionAssoc_runner))) ++ "}|]")).


Parameter OCamlString : Type.
Extract Constant OCamlString => "string".
Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""test_prop_InsertValid_runner"", qctest_test_prop_InsertValid_runner); (""test_prop_DeleteValid_runner"", qctest_test_prop_DeleteValid_runner); (""test_prop_UnionValid_runner"", qctest_test_prop_UnionValid_runner); (""test_prop_InsertPost_runner"", qctest_test_prop_InsertPost_runner); (""test_prop_DeletePost_runner"", qctest_test_prop_DeletePost_runner); (""test_prop_UnionPost_runner"", qctest_test_prop_UnionPost_runner); (""test_prop_InsertModel_runner"", qctest_test_prop_InsertModel_runner); (""test_prop_DeleteModel_runner"", qctest_test_prop_DeleteModel_runner); (""test_prop_UnionModel_runner"", qctest_test_prop_UnionModel_runner); (""test_prop_InsertInsert_runner"", qctest_test_prop_InsertInsert_runner); (""test_prop_InsertDelete_runner"", qctest_test_prop_InsertDelete_runner); (""test_prop_InsertUnion_runner"", qctest_test_prop_InsertUnion_runner); (""test_prop_DeleteInsert_runner"", qctest_test_prop_DeleteInsert_runner); (""test_prop_DeleteDelete_runner"", qctest_test_prop_DeleteDelete_runner); (""test_prop_DeleteUnion_runner"", qctest_test_prop_DeleteUnion_runner); (""test_prop_UnionDeleteInsert_runner"", qctest_test_prop_UnionDeleteInsert_runner); (""test_prop_UnionUnionIdem_runner"", qctest_test_prop_UnionUnionIdem_runner); (""test_prop_UnionUnionAssoc_runner"", qctest_test_prop_UnionUnionAssoc_runner)
  ] in
  let test = List.assoc test_name test_map in
  test ()

let () =
Sys.argv.(1) |> qctest_map

".

Extraction "SpecificationBasedGenerator_test_runner.ml" qctest_test_prop_InsertValid_runner qctest_test_prop_DeleteValid_runner qctest_test_prop_UnionValid_runner qctest_test_prop_InsertPost_runner qctest_test_prop_DeletePost_runner qctest_test_prop_UnionPost_runner qctest_test_prop_InsertModel_runner qctest_test_prop_DeleteModel_runner qctest_test_prop_UnionModel_runner qctest_test_prop_InsertInsert_runner qctest_test_prop_InsertDelete_runner qctest_test_prop_InsertUnion_runner qctest_test_prop_DeleteInsert_runner qctest_test_prop_DeleteDelete_runner qctest_test_prop_DeleteUnion_runner qctest_test_prop_UnionDeleteInsert_runner qctest_test_prop_UnionUnionIdem_runner qctest_test_prop_UnionUnionAssoc_runner qctest_map.
