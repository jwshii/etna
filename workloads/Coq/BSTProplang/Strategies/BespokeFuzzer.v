From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From PropLang Require Import PropLang.
From BSTProplang Require Import Spec.
From BSTProplang Require Import Impl.

Local Open Scope nat.
Local Open Scope prop_scope.

Definition insert_correct (k : nat) (v: nat) (t : Tree) :=
  match t with
  | E => T E k v E
  | T l k' v' r =>       
    if k <? k' then T (insert k v l) k' v' r 
    else if k' <? k then T l k' v' (insert k v r) 
    else T l k' v r
  end.

Fixpoint gen_kvs (s : nat) (lo hi: nat) : G (list (nat * nat)) :=
	match s with
	| O => ret []
	| S s' => 
		if lo <? hi then
			bindGen (choose(lo, hi)%nat) (fun k =>
			bindGen arbitrary (fun v =>
			bindGen (gen_kvs s' lo hi) (fun kvs =>
			ret ((k, v) :: kvs))))
		else ret []
	end.

Definition gen_bst (s : nat) (lo hi: nat) : G Tree :=
	bindGen (choose(0, s)%nat) (fun sz =>
	bindGen (gen_kvs sz lo hi) (fun kvs =>
	ret (fold_right (fun '(k, v) t => insert_correct k v t) E kvs))).

	
Fixpoint mutate_bst_ (t : Tree) (lo hi: nat) : G Tree :=
  match t with
  | E => freq [(4, ret E)
              ;(1, gen_bst 1 lo hi)]
  | T l k v r => freq [	
	(4, l' <- mutate_bst_ l lo (k - 1);; ret (T l' k v r));
	(4, r' <- mutate_bst_ r (k + 1) hi;; ret (T l k v r'));
    (2, 
		let s := size l in
		l' <- gen_bst s lo (k - 1);;
		ret (T l' k v r));
	(2, 
		let s := size r in
		r' <- gen_bst s (k + 1) hi;;
		ret (T l k v r'));
	(1, v' <- arbitrary;;
		ret (T l k v' r))
		]
  end.

Definition bespoke := gen_bst 6 0 40.
Definition mutate_bst := (fun t => mutate_bst_ t 0 40).

Derive (Shrink, Show) for Tree.

Local Open Scope nat.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".


Definition prop_InsertValid   :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => (isBST (insert k v t))))))).

Definition test_prop_InsertValid := (fuzzLoop number_of_trials prop_InsertValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid   :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => (isBST (delete k t)))))).

Definition test_prop_DeleteValid := (fuzzLoop number_of_trials prop_DeleteValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteValid. *)

Definition prop_UnionValid :=
	ForAll "t1" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	ForAll "t2" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	Check (Tree · (Tree · ∅))
	(fun '(t2, (t1, _)) => (isBST (union t1 t2))))))).

Definition test_prop_UnionValid := (fuzzLoop number_of_trials prop_UnionValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionValid. *)

Definition prop_InsertPost :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition test_prop_InsertPost := (fuzzLoop number_of_trials prop_InsertPost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertPost. *)


Definition prop_DeletePost :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition test_prop_DeletePost := (fuzzLoop number_of_trials prop_DeletePost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeletePost. *)

Definition prop_UnionPost :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
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

Definition test_prop_UnionPost := (fuzzLoop number_of_trials prop_UnionPost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionPost. *)

Definition prop_InsertModel :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (fuzzLoop number_of_trials prop_InsertModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition test_prop_DeleteModel := (fuzzLoop number_of_trials prop_DeleteModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_UnionModel :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	Check (Tree · (Tree · ∅))
	(fun '(t', (t, _)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition test_prop_UnionModel := (fuzzLoop number_of_trials prop_UnionModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionModel. *)

Definition prop_InsertInsert :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (nat · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, _))))) => (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t))))))))).

Definition test_prop_InsertInsert := (fuzzLoop number_of_trials prop_InsertInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert. *)

Definition prop_InsertDelete :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition test_prop_InsertDelete := (fuzzLoop number_of_trials prop_InsertDelete (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_InsertUnion :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition test_prop_InsertUnion := (fuzzLoop number_of_trials prop_InsertUnion (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertUnion. *)

Definition prop_DeleteInsert :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v', (k', (k, (t, _)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition test_prop_DeleteInsert := (fuzzLoop number_of_trials prop_DeleteInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition test_prop_DeleteDelete := (fuzzLoop number_of_trials prop_DeleteDelete (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete. *)

Definition prop_DeleteUnion :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, _))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition test_prop_DeleteUnion := (fuzzLoop number_of_trials prop_DeleteUnion (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteUnion. *)

Definition prop_UnionDeleteInsert :=
	ForAll "t " (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "t'" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition test_prop_UnionDeleteInsert := (fuzzLoop number_of_trials prop_UnionDeleteInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionDeleteInsert. *)

Definition prop_UnionUnionIdem :=
	ForAll "t" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	Check (Tree · ∅)
	(fun '(t, _) => (union t t =|= t)))).

Definition test_prop_UnionUnionIdem := (fuzzLoop number_of_trials prop_UnionUnionIdem (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionIdem. *)

Definition prop_UnionUnionAssoc :=
	ForAll "t1" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	ForAll "t2" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	ForAll "t3" (fun _ => bespoke) (fun _ => mutate_bst) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t3, _) => isBST t3) (
	Check (Tree · (Tree · (Tree · ∅)))
	(fun '(t3, (t2, (t1, _))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition test_prop_UnionUnionAssoc := (fuzzLoop number_of_trials prop_UnionUnionAssoc (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionAssoc. *)

