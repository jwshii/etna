From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Local Open Scope prop_scope.

Require Import TestingCommon.
Require Import Reachability.
Require Import SSNI.
Require Import SanityChecks.
Require Import VariationalGenerator.
Require Import BespokeGenerator.

Require Import List.
Import ListNotations.

Require Import ZArith.
(* Require Import Generation. *)
From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.


#[local] Instance FuzzyZ : Fuzzy Z :=
  {| fuzz n := choose (n - 5, n + 5)%Z |}.


Derive (GenSized, Show, Shrink) for Instr.
Derive (GenSized, Show, Shrink) for Pointer.
Derive (GenSized, Show, Shrink) for Value.
Derive (GenSized, Show, Shrink) for Atom.
Derive (GenSized, Show, Shrink) for Ptr_atom.
Derive (GenSized, Show, Shrink) for StackFrame.
Derive (GenSized, Show, Shrink) for Stack.
Derive (GenSized, Show, Shrink) for SState.
Derive (GenSized, Show, Shrink) for Variation.


Search Variation.

Axiom num_tests : nat. 
Extract Constant num_tests => "max_int".


Definition mutate_instructions (im: list Instr) (st: SState) (lab: Label) : G (list (@Instr Label)) :=
  freq_ (ret im) [
    (* Generate from scratch *) 
    (1, generate_instructions 10) 
    (* Delete a portion *)
    ; (2, 
      bindGen (choose (0, length im)) (fun n =>
      bindGen (choose (0, length im - n)) (fun i =>
      ret (take n im ++ drop (n + i) im)))
    )
    (* Modify a portion *)
    ; (2, 
      bindGen (choose (0, length im)) (fun n =>
      bindGen (choose (0, length im - n)) (fun i =>
      bindGen (generate_instructions n) (fun im' =>
      ret (take n im ++ im' ++ drop (n + i) im))))
    )
    (* Insert a portion *)
    ; (2, 
      bindGen (choose (0, length im)) (fun i =>
      bindGen (choose (1, 10)) (fun n =>
      bindGen (generate_instructions n) (fun im' =>
      ret (take n im ++ im' ++ drop n im))))
    )
  ].



Definition gen_variation_copy : G (@Variation SState) :=
  bindGen arbitrary (fun l  =>
  bindGen arbitrary (fun st =>
  bindGen (generate_instructions 10) (fun im =>
  let '(St _ m s r pc) := st in
  returnGen (Var l (St im m s r pc) st)))).

Definition mutate_variation (v: @Variation SState) : G (@Variation SState) :=
  let '(Var l st1 st2) := v in
  let '(St im m s r pc) := st1 in
  bindGen (mutate_instructions im st1 l) (fun im' =>
  returnGen (Var l (St im' m s r pc) st2)).

Definition test_propEENI :=
  @targetLoop 
    number_of_trials 
    (ForAll "v" (fun _ => gen_variation_copy) (fun _ => mutate_variation) (fun _ => (@shrink _ ShrinkVariation)) (fun _ => @show _ ShowVariation) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => indist lab st1 st2) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st1) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st2) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => is_some (fst (fstep_trans 30 default_table st1))) (
    Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => is_some (fst (fstep_trans 30 default_table st2))) (
    Check ((@Variation SState) · ∅) (fun '(Var lab st1 st2, _) => 
      let st1' := unwrap_or (fst (fstep_trans 30 default_table st1)) st1 in
      let st2' := unwrap_or (fst (fstep_trans 30 default_table st2)) st2 in
      indist lab st1' st2' && well_formed st1' && well_formed st2'
    ))))))))
    (fun '((Var lab st1 st2), _) => 
    let run_length_1 := snd (fstep_trans 30 default_table st1) in
    let run_length_2 := snd (fstep_trans 30 default_table st2) in
      Z.of_nat run_length_1)
      _ _
    (HeapSeedPool.(mkPool) tt) 
    HillClimbingUtility.

Sample test_propEENI.
  
(*! QuickProp test_propEENI. *)