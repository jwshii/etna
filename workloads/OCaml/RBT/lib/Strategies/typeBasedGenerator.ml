open Spec
open Impl
open QCheck

(* --------------------- Generator --------------------- *)

let typebased =
  let open QCheck.Gen in
  let t c l k v r = T (c, l, k, v, r) in
  let rec tree_gen n =
    if n <= 0 then return E
    else
      Gen.(
        t
        <$> frequency [ (1, return R); (1, return B) ]
        <*> tree_gen (n / 2)
        <*> nat <*> nat
        <*> tree_gen (n / 2))
  in
  sized (fun n -> tree_gen n)

let rec print_tree t =
  match t with
  | E -> "Empty"
  | T (c, l, k, v, r) ->
      let cs = if c = R then "R" else "B" in
      "Tree (" ^ cs ^ "," ^ print_tree l ^ "," ^ string_of_int k ^ ","
      ^ string_of_int v ^ "," ^ print_tree r ^ ")"

let aKey = small_int
let aVal = small_int
let makeTest name = Test.make ~count:1000 ~name
let arbitrary_of_gen g = make g ~print:print_tree

(* --------------------- Tests --------------------- *)

(* discarded "None" tests should be considered passing *)
let ( ~~ ) x = match x with Some false -> false | _ -> true

let test_prop_InsertValid aTree =
  makeTest "test_prop_InsertValid" (triple aTree aKey aVal) (fun (t, k, v) ->
      prop_InsertValid t k v)

(*! QCheck test_prop_InsertValid. *)

let test_prop_DeleteValid aTree =
  makeTest "test_prop_DeleteValid" (pair aTree aKey) (fun (t, k) ->
      ~~(prop_DeleteValid t k))

(*! QCheck test_prop_DeleteValid. *)

let test_prop_InsertPost aTree =
  makeTest "test_prop_InsertPost" (quad aTree aKey aKey aVal)
    (fun (t, k, k', v) -> prop_InsertPost t k k' v)

(*! QCheck test_prop_InsertPost. *)

let test_prop_DeletePost aTree =
  makeTest "test_prop_DeletePost" (triple aTree aKey aKey) (fun (t, k, k') ->
      prop_DeletePost t k k')

(*! QCheck test_prop_DeletePost. *)

let test_prop_InsertModel aTree =
  makeTest "test_prop_InsertModel" (triple aTree aKey aVal) (fun (t, k, v) ->
      prop_InsertModel t k v)

(*! QCheck test_prop_InsertModel. *)

let test_prop_DeleteModel aTree =
  makeTest "test_prop_DeleteModel" (pair aTree aKey) (fun (t, k) ->
      ~~(prop_DeleteModel t k))

(*! QCheck test_prop_DeleteModel. *)

let test_prop_InsertInsert aTree =
  makeTest "test_prop_InsertInsert"
    (triple aTree (pair aKey aKey) (pair aVal aVal))
    (fun (t, (k, k'), (v, v')) -> prop_InsertInsert t k k' v v')

(*! QCheck test_prop_InsertInsert. *)

let test_prop_InsertDelete aTree =
  makeTest "test_prop_InsertDelete" (quad aTree aKey aKey aVal)
    (fun (t, k, k', v) -> ~~(prop_InsertDelete t k k' v))

(*! QCheck test_prop_InsertDelete. *)

let test_prop_DeleteInsert aTree =
  makeTest "test_prop_DeleteInsert" (quad aTree aKey aKey aVal)
    (fun (t, k, k', v') -> ~~(prop_DeleteInsert t k k' v'))

(*! QCheck test_prop_DeleteInsert. *)

let test_prop_DeleteDelete aTree =
  makeTest "test_prop_DeleteDelete" (triple aTree aKey aKey) (fun (t, k, k') ->
      ~~(prop_DeleteDelete t k k'))

(*! QCheck test_prop_DeleteDelete. *)
