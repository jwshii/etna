
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
  bindGen (generate_instructions 10) (fun im =>
  let '(St _ m s r pc) := st in
  returnGen (Var l (St im m s r pc) st)))).

  Definition test_propEENI :=
    runLoop number_of_trials (
    ForAll "v" (fun _ => gen_variation_copy) (fun _ _ => gen_variation_copy) (fun _ => shrink) (fun _ => show) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => indist lab st1 st2) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st1) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st2) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => is_some (fst (fstep_trans 30 default_table st1))) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => is_some (fst (fstep_trans 30 default_table st2))) (
    Check ((@Variation SState) · ∅) (fun '(Var lab st1 st2, _) => 
      let st1' := unwrap_or (fst (fstep_trans 30 default_table st1)) st1 in
      let st2' := unwrap_or (fst (fstep_trans 30 default_table st2)) st2 in
      indist lab st1' st2' && well_formed st1' && well_formed st2'
    )))))))).
  
(* Sample test_propEENI. *)
(*! QuickProp test_propEENI. *)
  