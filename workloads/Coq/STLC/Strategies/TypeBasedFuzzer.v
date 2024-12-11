 
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Derive (Arbitrary, Fuzzy) for Typ.

Derive (Sized, Fuzzy) for nat.

Derive (Fuzzy) for bool.

Derive (Arbitrary, Fuzzy) for Expr.

Axiom num_tests : nat. Extract Constant num_tests => "max_int".

Definition test_prop_SinglePreserve (e: Expr) :=
    prop_SinglePreserve e.

Definition test_prop_SinglePreserve_fuzzer :=
    fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_SinglePreserve.
    
(*! FuzzChick test_prop_SinglePreserve (test_prop_SinglePreserve_fuzzer tt). *)

Definition test_prop_MultiPreserve (e: Expr) :=
    prop_MultiPreserve e.

Definition test_prop_MultiPreserve_fuzzer :=
    fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_MultiPreserve.
    
(*! FuzzChick test_prop_MultiPreserve (test_prop_MultiPreserve_fuzzer tt). *)
    
