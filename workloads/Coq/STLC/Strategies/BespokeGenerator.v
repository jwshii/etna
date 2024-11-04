 
From QuickChick Require Import QuickChick. Import QcNotation.

From STLC Require Import Impl Spec BespokeGeneration.

Definition test_prop_SinglePreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)