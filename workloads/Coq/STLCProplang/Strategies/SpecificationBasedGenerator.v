 
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLCProplang Require Import PropLang Impl Spec.
Local Open Scope prop_scope.

Derive (Arbitrary) for Typ.
Derive (Arbitrary) for Expr.


Inductive bind : Ctx -> nat -> Typ -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.
Inductive typing (G : Ctx) : Expr -> Typ -> Prop :=
| TyVar :
    forall x T,
      bind G x T ->
      typing G (Var x) T
| TyBool :
    forall b,
      typing G (Bool b) TBool
| TyAbs :
    forall e T1 T2,
      typing (T1 :: G) e T2 ->
      typing G (Abs T1 e) (TFun T1 T2)
| TyApp :
    forall e1 e2 T1 T2,
      typing G e1 (TFun T1 T2) ->
      typing G e2 T1 ->
      typing G (App e1 e2) T2.


#[export] Instance dec_type (t1 t2 : Typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive Arbitrary for Typ.
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
Derive ArbitrarySizedSuchThat for (fun t => typing env t tau).

Definition gTypedExpr G T sz :=
  @arbitrarySizeST _ (fun e => typing G e T) _ sz.


Definition gSized := 
    typ <- arbitrary ;;
    gTypedExpr [] typ 5.


#[local] Instance dec_eq_expr : Dec_Eq Expr.
Proof. dec_eq. Defined.
    
Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition test_prop_SinglePreserve   :=
  @ForAllMaybe _ ∅ _ "e" (fun tt => gSized) (fun tt n => (fun n => gSized)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (Expr · ∅) Z
  (fun '(e, tt) => (prop_SinglePreserve e, 0%Z))).

Definition test_prop_SinglePreserve_runner := (targetLoop number_of_trials test_prop_SinglePreserve (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_SinglePreserve_runner. *)
  

Definition test_prop_MultiPreserve   :=
  @ForAllMaybe _ ∅ _ "e" (fun tt => gSized) (fun tt n => (fun n => gSized)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (Expr · ∅) Z
  (fun '(e, tt) => (prop_MultiPreserve e, 0%Z))).

Definition test_prop_MultiPreserve_runner := (targetLoop number_of_trials test_prop_MultiPreserve (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_MultiPreserve_runner. *)