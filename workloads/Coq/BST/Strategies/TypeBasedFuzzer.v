From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

#[local] Instance FuzzyNat : Fuzzy nat :=
  {| fuzz n := choose (n - 5, n + 5) |}.

Derive (Arbitrary, Show, Sized, Fuzzy) for Tree.

#[local] Instance FuzzyProd {A} `{Fuzzy A} {B} `{Fuzzy B}  : Fuzzy (A * B)  :=
{|
  fuzz ab :=
    (let '(a, b) := ab in
    ma <- fuzz a ;;
    mb <- fuzz b ;;
    ret (ma,mb))
|}.

(* ManualExtract Tree. *)

(* QuickChickDebug Debug On. *)
(*|toggle|*)Axiom num_tests : nat. Extract Constant num_tests => "max_int".

Definition test_prop_InsertValid (tkv: (Tree * nat * nat)) :=
  let '(t, k, v) := tkv in
  prop_InsertValid t k v.

Definition test_prop_InsertValid_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertValid.

(*! FuzzChick test_prop_InsertValid (test_prop_InsertValid_fuzzer tt). *)


Definition test_prop_DeleteValid (tk: Tree * nat)  :=
  let '(t, k) := tk in
  prop_DeleteValid t k.

Definition test_prop_DeleteValid_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteValid.

(*! FuzzChick test_prop_DeleteValid (test_prop_DeleteValid_fuzzer tt). *)


Definition test_prop_UnionValid (t1t2: Tree * Tree)  :=
  let '(t1, t2) := t1t2 in
  prop_UnionValid t1 t2.

Definition test_prop_UnionValid_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionValid.

(*! FuzzChick test_prop_UnionValid (test_prop_UnionValid_fuzzer tt). *)

Definition test_prop_InsertPost (tkkpv: Tree * nat * nat * nat) :=
  let '(t, k, k', v) := tkkpv in
  prop_InsertPost t k k' v.

Definition test_prop_InsertPost_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertPost.

(*! FuzzChick test_prop_InsertPost (test_prop_InsertPost_fuzzer tt). *)

Definition test_prop_DeletePost (tkkp: Tree * nat * nat) :=
  let '(t, k, k') := tkkp in
  prop_DeletePost t k k.

Definition test_prop_DeletePost_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeletePost.

(*! FuzzChick test_prop_DeletePost (test_prop_DeletePost_fuzzer tt). *)

Definition test_prop_UnionPost (ttpk: Tree * Tree * nat)  :=
  let '(t, t', k) := ttpk in
  prop_UnionPost t t' k.

Definition test_prop_UnionPost_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionPost.

(*! FuzzChick test_prop_UnionPost (test_prop_UnionPost_fuzzer tt). *)

Definition test_prop_InsertModel (tkv: Tree * nat * nat)  :=
  let '(t, k, v) := tkv in
  prop_InsertModel t k v.

Definition test_prop_InsertModel_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertModel.

(*! FuzzChick test_prop_InsertModel (test_prop_InsertModel_fuzzer tt). *)

Definition test_prop_DeleteModel (tk: Tree * nat)  :=
  let '(t, k) := tk in
  prop_DeleteModel t k.

Definition test_prop_DeleteModel_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteModel.

(*! FuzzChick test_prop_DeleteModel (test_prop_DeleteModel_fuzzer tt). *)

Definition test_prop_UnionModel (ttp: Tree * Tree) :=
  let '(t, t') := ttp in
  prop_UnionModel t t'.

Definition test_prop_UnionModel_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionModel.

(*! FuzzChick test_prop_UnionModel (test_prop_UnionModel_fuzzer tt). *)

Definition test_prop_InsertInsert (tkkpvvp: Tree * nat * nat * nat * nat)   :=
  let '(t, k, k', v, v') := tkkpvvp in
  prop_InsertInsert t k k' v v.

Definition test_prop_InsertInsert_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertInsert.

(*! FuzzChick test_prop_InsertInsert (test_prop_InsertInsert_fuzzer tt). *)

Definition test_prop_InsertDelete (tkkpv: Tree * nat * nat * nat)  :=
  let '(t, k, k', v) := tkkpv in
  prop_InsertDelete t k k' v.

Definition test_prop_InsertDelete_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertDelete.

(*! FuzzChick test_prop_InsertDelete (test_prop_InsertDelete_fuzzer tt). *)

Definition test_prop_InsertUnion (ttpkv: Tree * Tree * nat * nat) :=
  let '(t, t', k, v) := ttpkv in
  prop_InsertUnion t t' k v.

Definition test_prop_InsertUnion_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertUnion.

(*! FuzzChick test_prop_InsertUnion (test_prop_InsertUnion_fuzzer tt). *)

Definition test_prop_DeleteInsert (tkkpvp: Tree * nat * nat * nat) :=
  let '(t, k, k', v') := tkkpvp in
  prop_DeleteInsert t k k' v'.

Definition test_prop_DeleteInsert_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteInsert.

(*! FuzzChick test_prop_DeleteInsert (test_prop_DeleteInsert_fuzzer tt). *)

Definition test_prop_DeleteDelete (tkkp: Tree * nat * nat) :=
  let '(t, k, k') := tkkp in
  prop_DeleteDelete t k k'.

Definition test_prop_DeleteDelete_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteDelete.

(*! FuzzChick test_prop_DeleteDelete (test_prop_DeleteDelete_fuzzer tt). *)

Definition test_prop_DeleteUnion (ttpk: Tree * Tree * nat) :=
  let '(t, t', k) := ttpk in
  prop_DeleteUnion t t' k.

Definition test_prop_DeleteUnion_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteUnion.

(*! FuzzChick test_prop_DeleteUnion (test_prop_DeleteUnion_fuzzer tt). *)

Definition test_prop_UnionDeleteInsert (ttpkv: Tree * Tree * nat * nat) :=
  let '(t, t', k, v) := ttpkv in
  prop_UnionDeleteInsert t t' k v.

Definition test_prop_UnionDeleteInsert_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionDeleteInsert.

(*! FuzzChick test_prop_UnionDeleteInsert (test_prop_UnionDeleteInsert_fuzzer tt). *)

Definition test_prop_UnionUnionIdem (t: Tree) :=
  prop_UnionUnionIdem t.

Definition test_prop_UnionUnionIdem_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionUnionIdem.

(*! FuzzChick test_prop_UnionUnionIdem (test_prop_UnionUnionIdem_fuzzer tt). *)

Definition test_prop_UnionUnionAssoc (t1t2t3 : Tree * Tree * Tree) :=
  let '(t1, t2, t3) := t1t2t3 in
  prop_UnionUnionAssoc t1 t2 t3.

Definition test_prop_UnionUnionAssoc_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_UnionUnionAssoc.

(*! FuzzChick test_prop_UnionUnionAssoc (test_prop_UnionUnionAssoc_fuzzer tt). *)
