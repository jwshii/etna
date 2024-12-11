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
Require Import Datatypes.
Require Import Coq.FSets.FMapFacts.
(* Require Import Generation. *)
From mathcomp Require Import ssreflect eqtype seq.
Import LabelEqType.


#[local] Instance FuzzyZ : Fuzzy Z :=
  {| fuzz n := choose (n - 5, n + 5)%Z |}.


  Derive (GenSized, Fuzzy) for BinOpT.
Derive (GenSized, Fuzzy) for Instr.
Derive (GenSized, Fuzzy) for Pointer.
Derive (GenSized, Fuzzy) for Value.
Derive (GenSized, Fuzzy) for Atom.
Derive (GenSized, Fuzzy) for Ptr_atom.
Derive (GenSized, Fuzzy) for StackFrame.
Derive (GenSized, Fuzzy) for Stack.
Derive (GenSized, Fuzzy) for SState.


Axiom num_tests : nat. 
Extract Constant num_tests => "max_int".


Definition mutate_instructions (im: imem) : G (list (@Instr Label)) :=
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
  returnGen (Var l st st))).


Definition mutate_variation (v: @Variation SState) : G (@Variation SState) :=
  let '(Var l st1 st2) := v in
  let '(St im1 m1 s1 r1 pc1) := st1 in
  let '(St im2 m2 s2 r2 pc2) := st2 in
  bindGen (mutate_instructions im1) (fun im =>
  bindGen (fuzz m1) (fun m => 
  ret (Var l (St im m s1 r1 pc1) (St im m s2 r2 pc2)))).


Fixpoint step_until_low (fuel: nat) (t: table) (l: Label) (st: SState) (s: nat) : ((option SState) * nat) :=
  match fuel with
  | 0 => (None, s)
  | S n' =>
    match is_low_SState st l with
    | true => (Some st, S s)
    | false =>
      match fstep t st with
      | Some st' => 
        let '(res, run_length) := step_until_low n' t l st' s in
        (res, S run_length)
      | None => (None, s)
      end
    end
  end.

Definition propLLNI :=
  ForAll "v" (fun _ => gen_variation_copy) (fun _ => mutate_variation) (fun _ => shrink) (fun _ => show) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => indist lab st1 st2) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st1) (
  Implies ((@Variation SState) · ∅) (fun '((Var lab st1 st2), _) => well_formed st2) (
  @ForAll (option (bool * nat)) ((@Variation SState) · ∅) "result" (fun '(v, _) => returnGen (low_indist 100 default_table v 0)) (fun '(v, _) _ => returnGen (low_indist 100 default_table v 0)) (fun _ => shrink) (fun _ => show) (
  Implies ((option (bool * nat)) · _) (fun '(result, _) => is_some result) (
  Check ((option (bool * nat)) · _) (fun '(result, _) => 
    fst (unwrap_or result (false, 0))
  ))))))).

Definition test_propLLNI := targetLoop number_of_trials propLLNI (fun '(_, (result, _)) => Z.of_nat (snd (unwrap_or result (false, 0)))) (HeapSeedPool.(mkPool) tt) HillClimbingUtility.
(*! QuickProp test_propLLNI. *)