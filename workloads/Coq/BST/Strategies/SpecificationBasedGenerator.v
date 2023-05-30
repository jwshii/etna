From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import List. Import ListNotations.
From ExtLib Require Import Monad.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Inductive between : nat -> nat -> nat -> Prop :=
| between_n : forall n m, le n m -> between n (S n) (S (S m))
| between_S : forall n m o, between n m o -> between n (S m) (S o).

Derive DecOpt for (le x y).
Derive ArbitrarySizedSuchThat for (fun x => le y x).

Derive ArbitrarySizedSuchThat for (fun x => between lo x hi).
Derive DecOpt for (between lo x hi).

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi E
| bst_node : forall lo hi k v l r,
    between lo k hi ->
    bst lo k l -> bst k hi r ->
    bst lo hi (T l k v r).

Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).
Derive DecOpt for (bst lo hi t).


Definition test_prop_InsertValid   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertValid t k v)))
.


(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteValid t k))
.

(*! QuickChick test_prop_DeleteValid. *)


Definition test_prop_UnionValid    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t1 : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t2 : Tree) =>
  prop_UnionValid t1 t2))
.

(*! QuickChick test_prop_UnionValid. *)

Definition test_prop_InsertPost    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertPost t k k' v))))
.

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat) =>
  prop_DeletePost t k k')))
.

(*! QuickChick test_prop_DeletePost. *)

Definition test_prop_UnionPost   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t' : Tree) =>
  forAll arbitrary (fun (k: nat) =>
  prop_UnionPost t t' k)))
.

(*! QuickChick test_prop_UnionPost. *)

Definition test_prop_InsertModel   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertModel t k v)))
.

(*! QuickChick test_prop_InsertModel. *)

Definition test_prop_DeleteModel   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteModel t k))
.

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_UnionModel    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t' : Tree) =>
  prop_UnionModel t t'))
.

(*! QuickChick test_prop_UnionModel. *)

Definition test_prop_InsertInsert    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat)  =>
  forAll arbitrary (fun (v': nat) =>
  prop_InsertInsert t k k' v v')))))
.

(*! QuickChick test_prop_InsertInsert. *)

Definition test_prop_InsertDelete    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertDelete t k k' v))))
.

(*! QuickChick test_prop_InsertDelete. *)

Definition test_prop_InsertUnion   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t' : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  prop_InsertUnion t t' k v))))
.

(*! QuickChick test_prop_InsertUnion. *)

Definition test_prop_DeleteInsert    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat)  =>
  forAll arbitrary (fun (v': nat) =>
  prop_DeleteInsert t k k' v'))))
.

(*! QuickChick test_prop_DeleteInsert. *)

Definition test_prop_DeleteDelete    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (k': nat) =>
  (prop_DeleteDelete t k k'))))
.

(*! QuickChick test_prop_DeleteDelete. *)

Definition test_prop_DeleteUnion   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t' : Tree) =>
  forAll arbitrary (fun (k: nat) =>
  prop_DeleteUnion t t' k)))
.

(*! QuickChick test_prop_DeleteUnion. *)

Definition test_prop_UnionDeleteInsert   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t: Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t' : Tree) =>
  forAll arbitrary (fun (k: nat)  =>
  forAll arbitrary (fun (v: nat) =>
  (prop_UnionDeleteInsert t t' k v)))))
.

(*! QuickChick test_prop_UnionDeleteInsert. *)

Definition test_prop_UnionUnionIdem    :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t: Tree) =>
  prop_UnionUnionIdem t)
.

(*! QuickChick test_prop_UnionUnionIdem. *)

Definition test_prop_UnionUnionAssoc   :=
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t1 : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t2 : Tree) =>
  forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t3 : Tree) =>
  prop_UnionUnionAssoc t1 t2 t3)))
.

(*! QuickChick test_prop_UnionUnionAssoc. *)