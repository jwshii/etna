 
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLCProplang Require Import PropLang Impl Spec.
Local Open Scope prop_scope.


Derive (Arbitrary, Fuzzy) for Typ.

Derive (Sized, Fuzzy) for nat.

Derive (Fuzzy) for bool.

Derive (Arbitrary, Fuzzy) for Expr.



#[local] Instance dec_eq_expr : Dec_Eq Expr.
Proof. dec_eq. Defined.
    
Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition test_prop_SinglePreserve   :=
  @ForAll _ ∅ _ "e" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (Expr · ∅) Z
  (fun '(e, tt) => (prop_SinglePreserve e, 0%Z))).

Definition test_prop_SinglePreserve_runner := (targetLoop number_of_trials test_prop_SinglePreserve (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_SinglePreserve_runner. *)
  

Definition test_prop_MultiPreserve   :=
  @ForAll _ ∅ _ "e" (fun tt => arbitrary) (fun tt n => (fun n => fuzz n)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (Expr · ∅) Z
  (fun '(e, tt) => (prop_MultiPreserve e, 0%Z))).

Definition test_prop_MultiPreserve_runner := (targetLoop number_of_trials test_prop_MultiPreserve (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_MultiPreserve_runner. *)