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

#[local] Instance shrinkTree : Shrink Tree :=
{|
  shrink t := match t with
              | E => []
              | T l k v r => [l; r]
              end
|}.

Definition spec_derived := (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10).
Derive (Show) for Tree.

Local Open Scope Z.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "20000".

Definition test_prop_InsertValid   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertValid t k v, 0%Z))))).

Definition test_prop_InsertValid_runner := (targetLoop number_of_trials test_prop_InsertValid (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0%Z)))).

Definition test_prop_DeleteValid_runner := (targetLoop number_of_trials test_prop_DeleteValid (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_UnionValid    :=
	@ForAllMaybe _ ∅ _ "t1" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t2" (fun '(t1, tt) => spec_derived) (fun '(t1, tt) n => (fun n => spec_derived)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t2, (t1, tt)) => (prop_UnionValid t1 t2, 0%Z)))).

Definition test_prop_UnionValid_runner := (targetLoop number_of_trials test_prop_UnionValid (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (targetLoop number_of_trials test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (targetLoop number_of_trials test_prop_DeletePost (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_UnionPost   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t'" (fun '(t, tt) => spec_derived) (fun '(t, tt) n => (fun n => spec_derived)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_UnionPost t t' k, 0%Z))))).

Definition test_prop_UnionPost_runner := (targetLoop number_of_trials test_prop_UnionPost (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionPost_runner. *)

Definition test_prop_InsertModel   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

Definition test_prop_InsertModel_runner := (targetLoop number_of_trials test_prop_InsertModel (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

Definition test_prop_DeleteModel_runner := (targetLoop number_of_trials test_prop_DeleteModel (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_UnionModel    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t'" (fun '(t, tt) => spec_derived) (fun '(t, tt) n => (fun n => spec_derived)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t', (t, tt)) => (prop_UnionModel t t', 0%Z)))).

Definition test_prop_UnionModel_runner := (targetLoop number_of_trials test_prop_UnionModel (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (nat · (nat · (nat · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (nat · (nat · (nat · (nat · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (targetLoop number_of_trials test_prop_InsertInsert (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (targetLoop number_of_trials test_prop_InsertDelete (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete_runner. *)

Definition test_prop_InsertUnion   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t'" (fun '(t, tt) => spec_derived) (fun '(t, tt) n => (fun n => spec_derived)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t, tt))) => arbitrary) (fun '(k, (t', (t, tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t, tt))) n => shrink n) (fun '(k, (t', (t, tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => (prop_InsertUnion t t' k v, 0%Z)))))).

Definition test_prop_InsertUnion_runner := (targetLoop number_of_trials test_prop_InsertUnion (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertUnion_runner. *)

Definition test_prop_DeleteInsert    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (targetLoop number_of_trials test_prop_DeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (targetLoop number_of_trials test_prop_DeleteDelete (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete_runner. *)

Definition test_prop_DeleteUnion   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t'" (fun '(t, tt) => spec_derived) (fun '(t, tt) n => (fun n => spec_derived)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_DeleteUnion t t' k, 0%Z))))).

Definition test_prop_DeleteUnion_runner := (targetLoop number_of_trials test_prop_DeleteUnion (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteUnion_runner. *)

Definition test_prop_UnionDeleteInsert   :=
	@ForAllMaybe _ ∅ _ "t " (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t'" (fun '(t , tt) => spec_derived) (fun '(t , tt) n => (fun n => spec_derived)) (fun '(t , tt) n => shrink n) (fun '(t , tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t , tt)) => arbitrary) (fun '(t', (t , tt)) n => (fun n => arbitrary)) (fun '(t', (t , tt)) n => shrink n) (fun '(t', (t , tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t , tt))) => arbitrary) (fun '(k, (t', (t , tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t , tt))) n => shrink n) (fun '(k, (t', (t , tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => ((prop_UnionDeleteInsert t t' k v, 0%Z))))))).

Definition test_prop_UnionDeleteInsert_runner := (targetLoop number_of_trials test_prop_UnionDeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionDeleteInsert_runner. *)

Definition test_prop_UnionUnionIdem    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@Predicate (Tree · ∅) Z
	(fun '(t, tt) => (prop_UnionUnionIdem t, 0%Z))).

Definition test_prop_UnionUnionIdem_runner := (targetLoop number_of_trials test_prop_UnionUnionIdem (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionIdem_runner. *)

Definition test_prop_UnionUnionAssoc   :=
	@ForAllMaybe _ ∅ _ "t1" (fun tt => spec_derived) (fun tt n => (fun n => spec_derived)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAllMaybe _ (Tree · ∅) _ "t2" (fun '(t1, tt) => spec_derived) (fun '(t1, tt) n => (fun n => spec_derived)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@ForAllMaybe _ (Tree · (Tree · ∅)) _ "t3" (fun '(t2, (t1, tt)) => spec_derived) (fun '(t2, (t1, tt)) n => (fun n => spec_derived)) (fun '(t2, (t1, tt)) n => shrink n) (fun '(t2, (t1, tt)) n => show n) (
	@Predicate (Tree · (Tree · (Tree · ∅))) Z
	(fun '(t3, (t2, (t1, tt))) => (prop_UnionUnionAssoc t1 t2 t3, 0%Z))))).

Definition test_prop_UnionUnionAssoc_runner := (targetLoop number_of_trials test_prop_UnionUnionAssoc (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionAssoc_runner. *)
