
From QuickChick Require Import QuickChick. Import QcNotation.
From STLC Require Import Impl Spec TypeBasedGeneration.

Definition test_prop_SinglePreserve :=
  forAll arbitrary (fun (e: Expr) =>
    prop_SinglePreserve e).


(*! QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
  forAll arbitrary (fun (e: Expr) =>
    prop_MultiPreserve e).

(*! QuickChick test_prop_MultiPreserve. *)