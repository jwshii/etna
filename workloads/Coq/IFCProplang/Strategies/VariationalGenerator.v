
From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Local Open Scope prop_scope.

Require Import ZArith.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import SanityChecks.
Require Import BespokeGenerator.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition generate_instructions n : G (list (@Instr Label)) :=
  vectorOf n arbitrary.

Definition gen_variation_copy : G (@Variation SState) :=
  bindGen arbitrary (fun l  =>
  bindGen arbitrary (fun st =>
  returnGen (Var l st st))).

Definition propLLNI :=
  ForAll "v" (fun _ => gen_variation_copy) (fun _ _ => gen_variation_copy) (fun _ => shrink) (fun _ => show) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => indist lab st1 st2) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st1) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st2) (
  @ForAll (option (bool * nat)) ((@Variation SState) · ∅) "result" (fun '(v, _) => returnGen (low_indist 100 default_table v 0)) (fun '(v, _) _ => returnGen (low_indist 100 default_table v 0)) (fun _ => shrink) (fun _ => show) (
  Implies ((option (bool * nat)) · _) (fun '(result, _) => is_some result) (
  Check ((option (bool * nat)) · _) (fun '(result, _) => 
    fst (unwrap_or result (false, 0))
  ))))))).

Definition test_propLLNI := runLoop number_of_trials propLLNI.
(*! QuickProp test_propLLNI.  *)