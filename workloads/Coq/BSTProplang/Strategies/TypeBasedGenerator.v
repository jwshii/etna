From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BSTProplang Require Import Impl.
From BSTProplang Require Import Spec.
From PropLang Require Import PropLang.

Local Open Scope nat.
Local Open Scope prop_scope.

Derive (Arbitrary, Show) for Tree.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition prop_InsertValid   :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => (isBST (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).
(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid   :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => (isBST (delete k t)))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).

(*! QuickProp test_prop_DeleteValid. *)

Definition prop_UnionValid :=
	ForAll "t1" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	ForAll "t2" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	Check (Tree · (Tree · ∅))
	(fun '(t2, (t1, _)) => (isBST (union t1 t2))))))).

Definition test_prop_UnionValid := (runLoop number_of_trials prop_UnionValid).
(*! QuickProp test_prop_UnionValid. *)

Definition prop_InsertPost :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).
(*! QuickProp test_prop_InsertPost. *)


Definition prop_DeletePost :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)

Definition prop_UnionPost :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => arbitrary) (fun _ t' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, _))) => (let lhs := find k (union t t') in
									match (find k t) with
									| Some rhs => (lhs = (Some rhs))?
									| None => match (find k t') with
											| Some rhs => (lhs = (Some rhs))?
											| None => (lhs = None)?
											end
									end)))))).

Definition test_prop_UnionPost := (runLoop number_of_trials prop_UnionPost).
(*! QuickProp test_prop_UnionPost. *)

Definition prop_InsertModel :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_UnionModel :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => arbitrary) (fun _ t' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	Check (Tree · (Tree · ∅))
	(fun '(t', (t, _)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition test_prop_UnionModel := (runLoop number_of_trials prop_UnionModel).
(*! QuickProp test_prop_UnionModel. *)

Definition prop_InsertInsert :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (nat · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, _))))) => (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t))))))))).

Definition test_prop_InsertInsert := (runLoop number_of_trials prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert. *)

Definition prop_InsertDelete :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_InsertUnion :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => arbitrary) (fun _ t' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition test_prop_InsertUnion := (runLoop number_of_trials prop_InsertUnion).
(*! QuickProp test_prop_InsertUnion. *)

Definition prop_DeleteInsert :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v', (k', (k, (t, _)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)

Definition prop_DeleteUnion :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => arbitrary) (fun _ t' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, _))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition test_prop_DeleteUnion := (runLoop number_of_trials prop_DeleteUnion).
(*! QuickProp test_prop_DeleteUnion. *)

Definition prop_UnionDeleteInsert :=
	ForAll "t " (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => arbitrary) (fun _ t' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition test_prop_UnionDeleteInsert := (runLoop number_of_trials prop_UnionDeleteInsert).
(*! QuickProp test_prop_UnionDeleteInsert. *)

Definition prop_UnionUnionIdem :=
	ForAll "t" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	Check (Tree · ∅)
	(fun '(t, _) => (union t t =|= t)))).

Definition test_prop_UnionUnionIdem := (runLoop number_of_trials prop_UnionUnionIdem).
(*! QuickProp test_prop_UnionUnionIdem. *)

Definition prop_UnionUnionAssoc :=
	ForAll "t1" (fun _ => arbitrary) (fun _ t1 => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	ForAll "t2" (fun _ => arbitrary) (fun _ t2 => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	ForAll "t3" (fun _ => arbitrary) (fun _ t3 => arbitrary) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t3, _) => isBST t3) (
	Check (Tree · (Tree · (Tree · ∅)))
	(fun '(t3, (t2, (t1, _))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition test_prop_UnionUnionAssoc := (runLoop number_of_trials prop_UnionUnionAssoc).
(*! QuickProp test_prop_UnionUnionAssoc. *)

