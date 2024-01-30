From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

From BST Require Import PropLang.
Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BST Require Import Impl.
From BST Require Import Spec.

Local Open Scope nat.
Local Open Scope prop_scope.

Fixpoint gen_bst (s : nat) (lo hi : nat) : G Tree :=
  match s with
  | O => ret E
  | S s' => freq [(1, ret E)
                 ;(if hi - lo < 2? then 0 else s,
                    k <- choose (lo+1, hi-1);;
                    v <- arbitrary;;
                    l <- gen_bst s' lo k;;
                    r <- gen_bst s' k hi;;
                    ret (T l k v r))]
  end.

Fixpoint mutate_bst (t : Tree) : G Tree :=
  match t with
  | E => freq [(4, ret E)
              ;(1, gen_bst 1 0 10)]
  | T l k v r => freq [
    (1, ret t);
    (3, l' <- mutate_bst l;; ret (T l' k v r));
    (3, r' <- mutate_bst r;; ret (T l k v r'));
    (1, k' <- choose (k-1, k+1);;
        ret (T l k' v r));
    (1, v' <- arbitrary;;
        ret (T l k v' r))]
  end.

#[local] Instance shrinkTree : Shrink Tree :=
{|
  shrink t := match t with
              | E => []
              | T l k v r => [l; r]
              end
|}.
Definition bespoke := gen_bst 4 0 40.

Derive (Arbitrary, Show) for Tree.

Local Open Scope Z.
(* 
Definition test_prop_InsertPost :=
  @ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
              (fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))). *)


#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

(* Definition runner := (targetLoopLogged 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)
(* Definition runner := runLoop 200000 test_prop_InsertPost. *)
(* Sample1 runner. *)

(* Definition runner' := (targetLoopLogged 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)
(* Sample1 runner'. *)


Definition test_prop_InsertValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => 
	let '(res, feedback) := withInstrumentation (fun _ => prop_InsertValid t k v) in
	(res, Z.of_nat(snd feedback)))))).


Definition test_prop_InsertValid_runner := (targetLoop 20000 test_prop_InsertValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0%Z)))).

Definition test_prop_DeleteValid_runner := (targetLoop 20000 test_prop_DeleteValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_UnionValid    :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => arbitrary)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t2, (t1, tt)) => (prop_UnionValid t1 t2, 0%Z)))).

Definition test_prop_UnionValid_runner := (targetLoop 20000 test_prop_UnionValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (targetLoop 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (targetLoop 20000 test_prop_DeletePost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_UnionPost   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_UnionPost t t' k, 0%Z))))).

Definition test_prop_UnionPost_runner := (targetLoop 20000 test_prop_UnionPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionPost_runner. *)

Definition test_prop_InsertModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

Definition test_prop_InsertModel_runner := (targetLoop 20000 test_prop_InsertModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

Definition test_prop_DeleteModel_runner := (targetLoop 20000 test_prop_DeleteModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_UnionModel    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t', (t, tt)) => (prop_UnionModel t t', 0%Z)))).

Definition test_prop_UnionModel_runner := (targetLoop 20000 test_prop_UnionModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (nat · (nat · (nat · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (nat · (nat · (nat · (nat · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (targetLoop 20000 test_prop_InsertInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (targetLoop 20000 test_prop_InsertDelete (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete_runner. *)

Definition test_prop_InsertUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t, tt))) => arbitrary) (fun '(k, (t', (t, tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t, tt))) n => shrink n) (fun '(k, (t', (t, tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => (prop_InsertUnion t t' k v, 0%Z)))))).

Definition test_prop_InsertUnion_runner := (targetLoop 20000 test_prop_InsertUnion (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertUnion_runner. *)

Definition test_prop_DeleteInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (targetLoop 20000 test_prop_DeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (targetLoop 20000 test_prop_DeleteDelete (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete_runner. *)

Definition test_prop_DeleteUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_DeleteUnion t t' k, 0%Z))))).

Definition test_prop_DeleteUnion_runner := (targetLoop 20000 test_prop_DeleteUnion (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteUnion_runner. *)

Definition test_prop_UnionDeleteInsert   :=
	@ForAll _ ∅ _ "t " (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t , tt) => bespoke) (fun '(t , tt) n => (fun n => arbitrary)) (fun '(t , tt) n => shrink n) (fun '(t , tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t , tt)) => arbitrary) (fun '(t', (t , tt)) n => (fun n => arbitrary)) (fun '(t', (t , tt)) n => shrink n) (fun '(t', (t , tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t , tt))) => arbitrary) (fun '(k, (t', (t , tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t , tt))) n => shrink n) (fun '(k, (t', (t , tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => ((prop_UnionDeleteInsert t t' k v, 0%Z))))))).

Definition test_prop_UnionDeleteInsert_runner := (targetLoop 20000 test_prop_UnionDeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionDeleteInsert_runner. *)

Definition test_prop_UnionUnionIdem    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@Predicate (Tree · ∅) Z
	(fun '(t, tt) => (prop_UnionUnionIdem t, 0%Z))).

Definition test_prop_UnionUnionIdem_runner := (targetLoop 20000 test_prop_UnionUnionIdem (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionIdem_runner. *)

Definition test_prop_UnionUnionAssoc   :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => arbitrary)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "t3" (fun '(t2, (t1, tt)) => bespoke) (fun '(t2, (t1, tt)) n => (fun n => arbitrary)) (fun '(t2, (t1, tt)) n => shrink n) (fun '(t2, (t1, tt)) n => show n) (
	@Predicate (Tree · (Tree · (Tree · ∅))) Z
	(fun '(t3, (t2, (t1, tt))) => (prop_UnionUnionAssoc t1 t2 t3, 0%Z))))).

Definition test_prop_UnionUnionAssoc_runner := (targetLoop 20000 test_prop_UnionUnionAssoc (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionAssoc_runner. *)
