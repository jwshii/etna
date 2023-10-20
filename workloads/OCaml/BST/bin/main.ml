open BST.TypeBasedGenerator

let rec lookup l k =
  match l with
  | [] -> None
  | (k', v)::l' -> if k = k' then Some v else lookup l' k


let tests = [
  ("prop_InsertValid", test_prop_InsertValid);
  ("prop_DeleteValid", test_prop_DeleteValid);
  ("prop_UnionValid", test_prop_UnionValid);
  ("prop_InsertPost", test_prop_InsertPost);
  ("prop_DeletePost", test_prop_DeletePost);
  ("prop_UnionPost", test_prop_UnionPost);
  ("prop_InsertModel", test_prop_InsertModel);
  ("prop_DeleteModel", test_prop_DeleteModel);
  ("prop_UnionModel", test_prop_UnionModel);
  ("prop_InsertInsert", test_prop_InsertInsert);
  ("prop_InsertDelete", test_prop_InsertDelete);
  ("prop_InsertUnion", test_prop_InsertUnion);
  ("prop_DeleteInsert", test_prop_DeleteInsert);
  ("prop_DeleteDelete", test_prop_DeleteDelete);
  ("prop_DeleteUnion", test_prop_DeleteUnion);
  ("prop_UnionDeleteInsert", test_prop_UnionDeleteInsert);
  ("prop_UnionUnionIdem", test_prop_UnionUnionIdem);
  ("prop_UnionUnionAssoc", test_prop_UnionUnionAssoc)
];;

let execute (testname : string) (file : string) : unit =
  let test = lookup tests testname in
  match test with
  | None -> Printf.printf "Test %s not found\n" testname
  | Some test ->
    let oc = open_out_gen [Open_wronly; Open_append; Open_creat] 0o666 file in
    let _  = Printf.fprintf oc "[%s|\n" testname in
    let st = Sys.time () in
    let _  = QCheck_runner.run_tests [test] ~colors:false ~verbose:true ~out:oc in
    let dt = (Sys.time ()  -. st) *. 1000.0 in
    let _  = Printf.fprintf oc "|%s %.2f]\n" testname dt in
    close_out oc

let main () : unit =
  if Array.length Sys.argv >= 4 then
    let testname = Sys.argv.(2) in
    let filename = Sys.argv.(3) in
    let _ = Printf.printf "Executing test %s into file %s" testname filename in
    execute testname filename
  else
    Printf.printf "Not enough arguments were provided to `dune exec`\n"

let () = main ()

