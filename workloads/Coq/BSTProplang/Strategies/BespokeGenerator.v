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
Definition bespoke s := gen_bst s 0 100.

Derive (Show) for Tree.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Axiom Time : Type.
Extract Constant Time => "int".

Axiom getCurrentTime : unit -> Time.
Extract Constant getCurrentTime => "fun _ -> Unix.gettimeofday ()".

Axiom timePassed : Time -> Time -> nat.
Extract Constant timePassed => "fun t1 t2 -> ((Float.to_int ((t2 -. t1) *. 1000000.0)))".

Record TimedResult := mkTimedResult {
  result: Result;
  time : nat;
}.

Open Scope string_scope.
#[global] Instance showTimedResult : Show TimedResult :=
  {| show r := show (result r) ++ 
  				", ""time"": " ++ show (time r) |}.


Local Open Scope nat_scope.

Definition timedRunLoop (max_time : nat)  (cprop : CProp ∅): G TimedResult := 
	let start_time := getCurrentTime tt in
	let fix runLoop'
		(fuel : nat) 
		(cprop : CProp ∅) 
		(passed : nat)
		(discards: nat)
		: G TimedResult :=
	let current_time := getCurrentTime tt in
	if  max_time <=? (timePassed start_time current_time) then
		ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
	else
		match fuel with
		| O => ret (mkTimedResult (mkResult discards false passed []) (timePassed start_time current_time))
		| S fuel' => 
			res <- genAndRun cprop (Nat.log2 (passed + discards)%nat);;
			match res with
			| Normal seed false =>
				(* Fails *)
				let shrinkingResult := shrinkLoop 10 cprop seed in
				let printingResult := print cprop 0%nat shrinkingResult in
				ret (mkTimedResult (mkResult discards true (passed + 1) printingResult) (timePassed start_time current_time))
			| Normal _ true =>
				(* Passes *)
				runLoop' fuel' cprop (passed + 1)%nat discards
			| Discard _ _ => 
				(* Discard *)
				runLoop' fuel' cprop passed (discards + 1)%nat
			end
		end in
		runLoop' number_of_trials cprop 0%nat 0%nat
    .


Record PreciseResult := mkPreciseResult {
	presult: Result;
	execution_time : nat;
	generation_time : nat;
	shrinking_time : nat;
	total_time : nat;
}.

#[global] Instance showPreciseResult : Show PreciseResult :=
  {| show r := show (presult r) ++
			   """, ""execution_time"": " ++ show (execution_time r) ++
			   ", ""generation_time"": " ++ show (generation_time r) ++
			   ", ""shrinking_time"": " ++ show (shrinking_time r) ++
			   ", ""total_time"": " ++ show (total_time r) |}.


(* Definition preciseRunLoop (fuel: nat)  (cprop : CProp ∅): G PreciseResult := 
	let fix runLoop'
		(fuel : nat) 
		(cprop : CProp ∅) 
		(passed : nat)
		(discards: nat)
		(generation_time: nat)
		(execution_time: nat)
		: G PreciseResult :=
	let current_time := getCurrentTime tt in
		match fuel with
		| O => ret (mkPreciseResult (mkResult discards false passed []) execution_time generation_time 0 (execution_time + generation_time))
		| S fuel' => 
			input <- justGen cprop (Nat.log2 (passed + discards)%nat);;
			res <- jusRun cprop input;;
			match res with
			| Normal seed false =>
				(* Fails *)
				let shrinkingResultWithTime := withTime(fun _ => shrinkLoop 10 cprop seed) in
				let shrinkingResult := aug_res shrinkingResultWithTime in
				let shrinking_time := aug_time shrinkingResultWithTime in
				let printingResult := print cprop 0%nat shrinkingResult in
				ret (mkPreciseResult (mkResult discards true (passed + 1) printingResult) execution_time generation_time shrinking_time (execution_time + generation_time + shrinking_time))
			| Normal _ true =>
				(* Passes *)
				runLoop' fuel' cprop (passed + 1)%nat discards
			| Discard _ _ => 
				(* Discard *)
				runLoop' fuel' cprop passed (discards + 1)%nat
			end
		end in
		runLoop' fuel cprop 0%nat 0%nat
	.
	
		 *)

Definition prop_InsertValid   :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => (isBST (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).
(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid   :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => (isBST (delete k t)))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).
(*! QuickProp test_prop_DeleteValid. *)

Definition prop_UnionValid :=
	@ForAll _ ∅ "t1" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	@ForAll _ (Tree · ∅) "t2" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	Check (Tree · (Tree · ∅))
	(fun '(t2, (t1, _)) => (isBST (union t1 t2))))))).

Definition test_prop_UnionValid := (runLoop number_of_trials prop_UnionValid).
(*! QuickProp test_prop_UnionValid. *)

Definition prop_InsertPost :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).
(*! QuickProp test_prop_InsertPost. *)

Definition prop_DeletePost :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ _ => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ _ => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)

Definition prop_UnionPost :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	@ForAll _  (Tree · ∅) "t'" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
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
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, _)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_UnionModel :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	@ForAll _ (Tree · ∅) "t'" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	Check (Tree · (Tree · ∅))
	(fun '(t', (t, _)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition test_prop_UnionModel := (runLoop number_of_trials prop_UnionModel).
(*! QuickProp test_prop_UnionModel. *)

Definition prop_InsertInsert :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
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
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_InsertUnion :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	@ForAll _ (Tree · ∅) "t'" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition test_prop_InsertUnion := (runLoop number_of_trials prop_InsertUnion).
(*! QuickProp test_prop_InsertUnion. *)

Definition prop_DeleteInsert :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v', (k', (k, (t, _)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)

Definition prop_DeleteUnion :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	@ForAll _ (Tree · ∅) "t'" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, _))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition test_prop_DeleteUnion := (runLoop number_of_trials prop_DeleteUnion).
(*! QuickProp test_prop_DeleteUnion. *)

Definition prop_UnionDeleteInsert :=
	@ForAll _ ∅ "t " bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	@ForAll _ (Tree · ∅) "t'" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, _)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition test_prop_UnionDeleteInsert := (runLoop number_of_trials prop_UnionDeleteInsert).
(*! QuickProp test_prop_UnionDeleteInsert. *)

Definition prop_UnionUnionIdem :=
	@ForAll _ ∅ "t" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isBST t) (
	Check (Tree · ∅)
	(fun '(t, _) => (union t t =|= t)))).

Definition test_prop_UnionUnionIdem := (runLoop number_of_trials prop_UnionUnionIdem).
(*! QuickProp test_prop_UnionUnionIdem. *)

Definition prop_UnionUnionAssoc :=
	@ForAll _ ∅ "t1" bespoke (fun s _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t1, _) => isBST t1) (
	@ForAll _ (Tree · ∅)"t2" (fun '(_, s) => bespoke s) (fun '(_, s) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	@ForAll _ (Tree · (Tree · ∅)) "t3" (fun '(_, (_, s)) => bespoke s) (fun '(_, (_, s)) _ => bespoke s) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · _) (fun '(t3, _) => isBST t3) (
	Check (Tree · (Tree · (Tree · ∅)))
	(fun '(t3, (t2, (t1, _))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition test_prop_UnionUnionAssoc := (runLoop number_of_trials prop_UnionUnionAssoc).
(*! QuickProp test_prop_UnionUnionAssoc. *)

