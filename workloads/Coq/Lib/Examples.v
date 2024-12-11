
Require Import String.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.

From PropLang Require Import PropLang.

Local Open Scope prop_scope.
Local Open Scope string_scope.


Derive (Arbitrary, Show) for nat.

Definition test2 (x y : nat) : bool :=
  (negb (Nat.eqb y  x)).

Definition example2 :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt => mut) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, _) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, _)) => test2 x y))).

Definition example_test := (filePrintingRunLoop 100 example2 "/Users/akeles/Programming/projects/PbtBenchmark/etna/output.txt").

Extraction "example.ml" example_test.


