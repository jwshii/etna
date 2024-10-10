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

#[local] Instance FuzzyZ : Fuzzy Z :=
  {| fuzz n := choose (n - 5, n + 5)%Z |}.

Derive (Arbitrary, Fuzzy) for BinOpT.
Derive (Arbitrary, Fuzzy) for Instr.
Derive (Arbitrary, Fuzzy) for Pointer.
Derive (Arbitrary, Fuzzy) for Value.
Derive (Arbitrary, Fuzzy) for Atom.
Derive (Arbitrary, Fuzzy) for Ptr_atom.
Derive (Arbitrary, Fuzzy) for StackFrame.
Derive (Arbitrary, Fuzzy) for Stack.
Derive (Arbitrary, Fuzzy) for SState.
Derive (Arbitrary, Fuzzy) for Variation.

Definition propLLNI :=
  ForAll "v" (fun _ => arbitrary) (fun _ => fuzz) (fun _ => shrink) (fun _ => show) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => indist lab st1 st2) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st1) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st2) (
  @ForAll (option (bool * nat)) ((@Variation SState) · ∅) "result" (fun '(v, _) => returnGen (low_indist 100 default_table v 0)) (fun '(v, _) _ => returnGen (low_indist 100 default_table v 0)) (fun _ => shrink) (fun _ => show) (
  Implies ((option (bool * nat)) · _) (fun '(result, _) => is_some result) (
  Check ((option (bool * nat)) · _) (fun '(result, _) => 
    fst (unwrap_or result (false, 0))
  ))))))).

Definition test_propLLNI := fuzzLoop number_of_trials propLLNI (HeapSeedPool.(mkPool) tt) HillClimbingUtility.
(*! QuickProp test_propLLNI.  *)