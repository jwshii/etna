


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.


From RBTProplang Require Import Impl Spec PropLang.
Local Open Scope prop_scope.
(* --------------------- Generator --------------------- *)


#[local] Instance FuzzyColor : Fuzzy Color :=
{| fuzz c :=  oneOf[ret R ; ret B] |}.


#[local] Instance FuzzyZ : Fuzzy Z :=
{| fuzz z :=  (choose (z - 5, z + 5)%Z) |}.


Local Open Scope nat_scope.

#[local] Instance FuzzyNat : Fuzzy nat :=
{| fuzz n :=  (choose (n - 5, n + 5)) |}.

Derive (Arbitrary, Show, Sized, Fuzzy) for Tree.

#[local] Instance FuzzyProd {A} `{Fuzzy A} {B} `{Fuzzy B}  : Fuzzy (A * B)  :=
{| 
  fuzz ab := 
    (let '(a, b) := ab in
    ma <- fuzz a ;;
    mb <- fuzz b ;;
    ret (ma,mb))
|}.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.
    

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "20000".


(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid   :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertValid t k v, 0%Z))))).

Definition test_prop_InsertValid_runner := (targetLoop number_of_trials test_prop_InsertValid (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0%Z)))).

Definition test_prop_DeleteValid_runner := (targetLoop number_of_trials test_prop_DeleteValid (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).

(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (targetLoop number_of_trials test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (targetLoop number_of_trials test_prop_DeletePost (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_InsertModel    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v'" (fun '(v, (t, tt)) => arbitrary) (fun '(v, (t, tt)) n => (fun n => arbitrary)) (fun '(v, (t, tt)) n => shrink n) (fun '(v, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

    
Definition test_prop_InsertModel_runner := (targetLoop number_of_trials test_prop_InsertModel (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

    
Definition test_prop_DeleteModel_runner := (targetLoop number_of_trials test_prop_DeleteModel (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (Z · (Z · (Z · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (Z · (Z · (Z · (Z · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (targetLoop number_of_trials test_prop_InsertInsert (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (targetLoop number_of_trials test_prop_InsertDelete (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete_runner. *)


Definition test_prop_DeleteInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (targetLoop number_of_trials test_prop_DeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (targetLoop number_of_trials test_prop_DeleteDelete (DynamicResettingSingletonPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete_runner. *)