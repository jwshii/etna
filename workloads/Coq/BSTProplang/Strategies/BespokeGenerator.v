From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BSTProplang Require Import Impl.
From BSTProplang Require Import Spec.
From PropLang Require Import PropLang.

Local Open Scope prop_scope.

Definition insert_correct (k : nat) (v: nat) (t : Tree) :=
  match t with
  | E => T E k v E
  | T l k' v' r =>       
    if k <? k' then T (insert k v l) k' v' r 
    else if k' <? k then T l k' v' (insert k v r) 
    else T l k' v r
  end.


Definition gen_bst (s : nat) (lo hi : nat) : G Tree :=
	let fix gen_bst (s : nat) (lo hi : nat) (t: Tree) : G Tree :=
		match s with
		| O => ret t
		| S s' => 
			k <- choose (lo, hi);;
			v <- arbitrary;;
			let t' := insert_correct k v t in
			gen_bst s' lo hi t'
		end
	in
	gen_bst s lo hi E.


#[local] Instance shrinkTree : Shrink Tree :=
{|
  shrink t := match t with
              | E => []
              | T l k v r => [l; r]
              end
|}.
Definition bespoke := gen_bst 4 0 40.

Derive (Show) for Tree.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition prop_InsertValid   :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => (isBST (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).

(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid   :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, tt)) => (isBST (delete k t)))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).

(*! QuickProp test_prop_DeleteValid. *)

Definition prop_UnionValid :=
	ForAll "t1" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t1" (fun '(t1, tt) => isBST t1) (
	ForAll "t2" (fun tt => bespoke) (fun tt n => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t2" (fun '(t2, _) => isBST t2) (
	Check (Tree · (Tree · ∅))
	(fun '(t2, (t1, tt)) => (isBST (union t1 t2))))))).

Definition test_prop_UnionValid := (runLoop number_of_trials prop_UnionValid).
(*! QuickProp test_prop_UnionValid. *)

Definition prop_InsertPost :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt k' => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).

(*! QuickProp test_prop_InsertPost. *)

Definition prop_DeletePost :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)

Definition prop_UnionPost :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "t'" (fun tt => bespoke) (fun tt t' => bespoke) (fun tt => shrink) (fun tt => show) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, tt))) => (let lhs := find k (union t t') in
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
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, tt)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_UnionModel :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "t'" (fun tt => bespoke) (fun tt t' => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t'" (fun '(t', _) => isBST t') (
	Check (Tree · (Tree · ∅))
	(fun '(t', (t, tt)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition test_prop_UnionModel := (runLoop number_of_trials prop_UnionModel).
(*! QuickProp test_prop_UnionModel. *)

Definition prop_InsertInsert :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v' => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (nat · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, tt))))) => (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t))))))))).

Definition test_prop_InsertInsert := (runLoop number_of_trials prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert. *)

Definition prop_InsertDelete :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt k' => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_InsertUnion :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "t'" (fun tt => bespoke) (fun tt t' => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t'" (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, tt)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition test_prop_InsertUnion := (runLoop number_of_trials prop_InsertUnion).
(*! QuickProp test_prop_InsertUnion. *)

Definition prop_DeleteInsert :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v', (k', (k, (t, tt)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)

Definition prop_DeleteUnion :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "t'" (fun tt => bespoke) (fun tt t' => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t'" (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, tt))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition test_prop_DeleteUnion := (runLoop number_of_trials prop_DeleteUnion).
(*! QuickProp test_prop_DeleteUnion. *)

Definition prop_UnionDeleteInsert :=
	ForAll "t " (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	ForAll "t'" (fun tt => bespoke) (fun tt t' => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t'" (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, tt)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition test_prop_UnionDeleteInsert := (runLoop number_of_trials prop_UnionDeleteInsert).
(*! QuickProp test_prop_UnionDeleteInsert. *)

Definition prop_UnionUnionIdem :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t" (fun '(t, tt) => isBST t) (
	Check (Tree · ∅)
	(fun '(t, tt) => (union t t =|= t)))).

Definition test_prop_UnionUnionIdem := (runLoop number_of_trials prop_UnionUnionIdem).
(*! QuickProp test_prop_UnionUnionIdem. *)

Definition prop_UnionUnionAssoc :=
	ForAll "t1" (fun tt => bespoke) (fun tt t1 => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isBST t1" (fun '(t1, tt) => isBST t1) (
	ForAll "t2" (fun tt => bespoke) (fun tt t2 => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t2" (fun '(t2, _) => isBST t2) (
	ForAll "t3" (fun tt => bespoke) (fun tt t3 => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) "isBST t3" (fun '(t3, _) => isBST t3) (
	Check (Tree · (Tree · (Tree · ∅)))
	(fun '(t3, (t2, (t1, tt))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition test_prop_UnionUnionAssoc := (runLoop number_of_trials prop_UnionUnionAssoc).
(*! QuickProp test_prop_UnionUnionAssoc. *)

