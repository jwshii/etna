open Impl
open List


let rec insert_correct (k: int) (v: int) (t: tree) =
  match t with
  | E -> T (E, k, v, E)
  | T (l, k', v', r) ->
      if k < k' then T ((insert_correct k v l), k', v', r)
      else if k' < k then T (l, k', v', (insert_correct k v r))
      else T (l, k', v, r)


let bespoke =
  let open QCheck.Gen in
  list (pair nat nat) >>= (fun kvs -> return (fold_left (fun t (k, v) -> insert_correct k v t) E kvs))

(*! QCheck test_prop_InsertValid. *)
(*! QCheck test_prop_DeleteValid. *)
(*! QCheck test_prop_UnionValid. *)
(*! QCheck test_prop_InsertPost. *)
(*! QCheck test_prop_DeletePost. *)
(*! QCheck test_prop_UnionPost. *)
(*! QCheck test_prop_InsertModel. *)
(*! QCheck test_prop_DeleteModel. *)
(*! QCheck test_prop_UnionModel. *)
(*! QCheck test_prop_InsertInsert. *)
(*! QCheck test_prop_InsertDelete. *)
(*! QCheck test_prop_InsertUnion. *)
(*! QCheck test_prop_DeleteInsert. *)
(*! QCheck test_prop_DeleteDelete. *)
(*! QCheck test_prop_DeleteUnion. *)
(*! QCheck test_prop_UnionDeleteInsert. *)
(*! QCheck test_prop_UnionUnionIdem. *)
(*! QCheck test_prop_UnionUnionAssoc. *)


