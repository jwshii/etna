From QuickChick Require Import QuickChick.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import SanityChecks.
Require Import ZArith.
Require Import BespokeGenerator.
From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.


From PropLang Require Import PropLang.
Local Open Scope prop_scope.

Derive Arbitrary for BinOpT.
Derive Arbitrary for Instr.
Derive Arbitrary for Pointer.
Derive Arbitrary for Value.
Derive Arbitrary for Atom.
Derive Arbitrary for Ptr_atom.
Derive Arbitrary for StackFrame.
Derive Arbitrary for Stack.
Derive Arbitrary for SState.
Derive Arbitrary for Variation.

Definition propLLNI :=
  ForAll "v" (fun _ => arbitrary) (fun _ _ => arbitrary) (fun _ => shrink) (fun _ => show) (
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