From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BSTProplang Require Import Impl.
From BSTProplang Require Import Spec.
From BSTProplang Require Import PropLang.

Local Open Scope nat.
Local Open Scope prop_scope.


Fixpoint insert_correct (k : nat) (v: nat) (t : Tree) :=
  match t with
  | E => T E k v E
  | T l k' v' r =>       
    if k <? k' then T (insert k v l) k' v' r 
    else if k' <? k then T l k' v' (insert k v r) 
    else T l k' v r
  end.


Fixpoint gen_bst (s : nat) (lo hi : nat) : G Tree :=
	let fix gen_bst (s : nat) (lo hi : nat) (t: Tree) : G Tree :=
		match s with
		| O => ret t
		| S s' => 
			if (lo <? hi) then	
				k <- choose (lo, hi);;
				v <- arbitrary;;
				let t' := insert_correct k v t in
				gen_bst s' lo hi t'
			else
				ret t
		end
	in
	gen_bst s lo hi E.
	

Definition get_key (t : Tree) : option nat :=
  match t with
  | E => None
  | T l k v r => Some k
  end.

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

#[local] Instance shrinkTree : Shrink Tree :=
{|
  shrink t := match t with
              | E => []
              | T l k v r => [l; r]
              end
|}.

Definition bespoke := gen_bst 4 0 40.
Definition mutate_bst := (fun t => mutate_bst_ t 0 40).

Derive (Show) for Tree.

Local Open Scope Z.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.


Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition withInstrumentation' fn :=
	let '(res, feedback) := withInstrumentation fn in
	(res, Z.of_nat(snd feedback)).


Definition test_prop_InsertValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => withInstrumentation' (fun _ => prop_InsertValid t k v))))).

Definition test_prop_InsertValid_runner := (targetLoop number_of_trials test_prop_InsertValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => withInstrumentation' (fun _ => prop_DeleteValid t k)))).

Definition test_prop_DeleteValid_runner := (targetLoop number_of_trials test_prop_DeleteValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_UnionValid    :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => mutate_bst n)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t2, (t1, tt)) => withInstrumentation' (fun _ => prop_UnionValid t1 t2)))).

Definition test_prop_UnionValid_runner := (targetLoop number_of_trials test_prop_UnionValid (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => withInstrumentation' (fun _ => prop_InsertPost t k k' v)))))).

Definition test_prop_InsertPost_runner := (targetLoop number_of_trials test_prop_InsertPost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => withInstrumentation' (fun _ => prop_DeletePost t k k'))))).

Definition test_prop_DeletePost_runner := (targetLoop number_of_trials test_prop_DeletePost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_UnionPost   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => mutate_bst n)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => withInstrumentation' (fun _ => prop_UnionPost t t' k))))).

Definition test_prop_UnionPost_runner := (targetLoop number_of_trials test_prop_UnionPost (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionPost_runner. *)

Definition test_prop_InsertModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => withInstrumentation' (fun _ => prop_InsertModel t k v))))).

Definition test_prop_InsertModel_runner := (targetLoop number_of_trials test_prop_InsertModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => withInstrumentation' (fun _ => prop_DeleteModel t k)))).

Definition test_prop_DeleteModel_runner := (targetLoop number_of_trials test_prop_DeleteModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_UnionModel    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => mutate_bst n)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t', (t, tt)) => withInstrumentation' (fun _ => prop_UnionModel t t')))).

Definition test_prop_UnionModel_runner := (targetLoop number_of_trials test_prop_UnionModel (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (nat · (nat · (nat · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (nat · (nat · (nat · (nat · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => withInstrumentation' (fun _ => prop_InsertInsert t k k' v v'))))))).

Definition test_prop_InsertInsert_runner := (targetLoop number_of_trials test_prop_InsertInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => withInstrumentation' (fun _ => prop_InsertDelete t k k' v)))))).

Definition test_prop_InsertDelete_runner := (targetLoop number_of_trials test_prop_InsertDelete (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete_runner. *)

Definition test_prop_InsertUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => mutate_bst n)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t, tt))) => arbitrary) (fun '(k, (t', (t, tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t, tt))) n => shrink n) (fun '(k, (t', (t, tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => withInstrumentation' (fun _ => prop_InsertUnion t t' k v)))))).

Definition test_prop_InsertUnion_runner := (targetLoop number_of_trials test_prop_InsertUnion (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertUnion_runner. *)

Definition test_prop_DeleteInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => withInstrumentation' (fun _ => prop_DeleteInsert t k k' v')))))).

Definition test_prop_DeleteInsert_runner := (targetLoop number_of_trials test_prop_DeleteInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (withInstrumentation' (fun _ => prop_DeleteDelete t k k')))))).

Definition test_prop_DeleteDelete_runner := (targetLoop number_of_trials test_prop_DeleteDelete (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete_runner. *)

Definition test_prop_DeleteUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => mutate_bst n)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => withInstrumentation' (fun _ => prop_DeleteUnion t t' k))))).

Definition test_prop_DeleteUnion_runner := (targetLoop number_of_trials test_prop_DeleteUnion (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteUnion_runner. *)

Definition test_prop_UnionDeleteInsert   :=
	@ForAll _ ∅ _ "t " (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t , tt) => bespoke) (fun '(t , tt) n => (fun n => mutate_bst n)) (fun '(t , tt) n => shrink n) (fun '(t , tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t , tt)) => arbitrary) (fun '(t', (t , tt)) n => (fun n => arbitrary)) (fun '(t', (t , tt)) n => shrink n) (fun '(t', (t , tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t , tt))) => arbitrary) (fun '(k, (t', (t , tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t , tt))) n => shrink n) (fun '(k, (t', (t , tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => (withInstrumentation' (fun _ => prop_UnionDeleteInsert t t' k v))))))).

Definition test_prop_UnionDeleteInsert_runner := (targetLoop number_of_trials test_prop_UnionDeleteInsert (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionDeleteInsert_runner. *)

Definition test_prop_UnionUnionIdem    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@Predicate (Tree · ∅) Z
	(fun '(t, tt) => withInstrumentation' (fun _ => prop_UnionUnionIdem t))).

Definition test_prop_UnionUnionIdem_runner := (targetLoop number_of_trials test_prop_UnionUnionIdem (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionIdem_runner. *)

Definition test_prop_UnionUnionAssoc   :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => mutate_bst n)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "t3" (fun '(t2, (t1, tt)) => bespoke) (fun '(t2, (t1, tt)) n => (fun n => mutate_bst n)) (fun '(t2, (t1, tt)) n => shrink n) (fun '(t2, (t1, tt)) n => show n) (
	@Predicate (Tree · (Tree · (Tree · ∅))) Z
	(fun '(t3, (t2, (t1, tt))) => withInstrumentation' (fun _ => prop_UnionUnionAssoc t1 t2 t3))))).

Definition test_prop_UnionUnionAssoc_runner := (targetLoop number_of_trials test_prop_UnionUnionAssoc (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionAssoc_runner. *)
