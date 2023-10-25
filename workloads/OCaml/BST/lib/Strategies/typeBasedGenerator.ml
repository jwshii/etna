open Spec
open Impl
open QCheck

let typebased =
  let open QCheck.Gen in
  let rec tree_gen n =
    if n <= 0 then
      return E
    else
      frequency
        [ 1, return E;
          2, map2 (fun (left, right) (key, value) -> T (left, key, value, right))
                 (pair (tree_gen (n / 2)) (tree_gen (n / 2))) (pair nat nat)
        ]
  in
  sized (fun n -> tree_gen n)

let rec print_tree = function
  | E -> "Empty"
  | T (l, k, v, r) -> "Tree (" ^ (print_tree l) ^ "," ^ (string_of_int k) ^ "," ^ (string_of_int v) ^ "," ^ (print_tree r) ^ ")"

let aKey = small_int
let aVal = small_int

let makeTest name = Test.make ~count:1000 ~name:name

let test_prop_InsertValid aTree =
  makeTest "test_prop_InsertValid"
  (triple aTree aKey aVal)
  prop_InsertValid


(*! QCheck test_prop_InsertValid. *)

let test_prop_DeleteValid aTree =
  makeTest "test_prop_DeleteValid"
  (pair aTree aKey)
  prop_DeleteValid


(*! QCheck test_prop_DeleteValid. *)


let test_prop_UnionValid aTree =
  makeTest "test_prop_UnionValid"
  (pair aTree aTree)
  prop_UnionValid


(*! QCheck test_prop_UnionValid. *)

let test_prop_InsertPost aTree =
  makeTest "test_prop_InsertPost"
  (quad aTree aKey aKey aVal)
  prop_InsertPost


(*! QCheck test_prop_InsertPost. *)

let test_prop_DeletePost aTree =
  makeTest "test_prop_DeletePost"
  (triple aTree aKey aKey)
  prop_DeletePost


(*! QCheck test_prop_DeletePost. *)

let test_prop_UnionPost aTree =
  makeTest "test_prop_UnionPost"
  (triple aTree aTree aKey)
  prop_UnionPost


(*! QCheck test_prop_UnionPost. *)

let test_prop_InsertModel aTree =
  makeTest "test_prop_InsertModel"
  (triple aTree aKey aVal)
  prop_InsertModel


(*! QCheck test_prop_InsertModel. *)

let test_prop_DeleteModel aTree =
  makeTest "test_prop_DeleteModel"
  (pair aTree aKey)
  prop_DeleteModel


(*! QCheck test_prop_DeleteModel. *)

let test_prop_UnionModel aTree =
  makeTest "test_prop_UnionModel"
  (pair aTree aTree)
  prop_UnionModel


(*! QCheck test_prop_UnionModel. *)

let test_prop_InsertInsert aTree =
  makeTest "test_prop_InsertInsert"
  (pair aTree (quad aKey aKey aVal aVal))
  (fun (t, (k, k', v, v')) -> prop_InsertInsert (t, k, k', v, v'))


(*! QCheck test_prop_InsertInsert. *)

let test_prop_InsertDelete aTree =
  makeTest "test_prop_InsertDelete"
  (quad aTree aKey aKey aVal)
  prop_InsertDelete


(*! QCheck test_prop_InsertDelete. *)

let test_prop_InsertUnion aTree =
  makeTest "test_prop_InsertUnion"
  (quad aTree aTree aKey aVal)
  prop_InsertUnion


(*! QCheck test_prop_InsertUnion. *)

let test_prop_DeleteInsert aTree =
  makeTest "test_prop_DeleteInsert"
  (quad aTree aKey aKey aVal)
  prop_DeleteInsert


(*! QCheck test_prop_DeleteInsert. *)

let test_prop_DeleteDelete aTree =
  makeTest "test_prop_DeleteDelete"
  (triple aTree aKey aKey)
  prop_DeleteDelete


(*! QCheck test_prop_DeleteDelete. *)

let test_prop_DeleteUnion aTree =
  makeTest "test_prop_DeleteUnion"
  (triple aTree aTree aKey)
  prop_DeleteUnion


(*! QCheck test_prop_DeleteUnion. *)

let test_prop_UnionDeleteInsert aTree =
  makeTest "test_prop_UnionDeleteInsert"
  (quad aTree aTree aKey aVal)
  prop_UnionDeleteInsert


(*! QCheck test_prop_UnionDeleteInsert. *)

let test_prop_UnionUnionIdem aTree =
  makeTest "test_prop_UnionUnionIdem"
  aTree
  prop_UnionUnionIdem


(*! QCheck test_prop_UnionUnionIdem. *)

let test_prop_UnionUnionAssoc aTree =
  makeTest "test_prop_UnionUnionAssoc"
  (triple aTree aTree aTree)
  prop_UnionUnionAssoc


(*! QCheck test_prop_UnionUnionAssoc. *)



