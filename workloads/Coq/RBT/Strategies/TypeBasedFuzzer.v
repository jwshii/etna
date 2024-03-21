


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.


From RBT Require Import Impl Spec.

(* --------------------- Generator --------------------- *)


#[local] Instance FuzzyColor : Fuzzy Color :=
{| fuzz c :=  oneOf[ret R ; ret B] |}.


#[local] Instance FuzzyZ : Fuzzy Z :=
{| fuzz z :=  (choose (z - 5, z + 5)%Z) |}.


Local Open Scope nat_scope.

#[local] Instance FuzzyNat : Fuzzy nat :=
{| fuzz n :=  (choose (n - 5, n + 5)) |}.

Derive (Arbitrary, Show, Sized, Fuzzy) for Tree.



#[local] Instance FuzzyProd {A} `{Fuzzy A} {B} `{Fuzzy B}  : Fuzzy (A * B)  :=
{| 
  fuzz ab := 
    (let '(a, b) := ab in
    ma <- fuzz a ;;
    mb <- fuzz b ;;
    ret (ma,mb))
|}.

(*|toggle|*)Axiom num_tests : nat. Extract Constant num_tests => "max_int".

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid (tkv: (Tree * Z * Z)) :=
  let '(t, k, v) := tkv in
  prop_InsertValid t k v.

Definition test_prop_InsertValid_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertValid.

(*! FuzzChick test_prop_InsertValid (test_prop_InsertValid_fuzzer tt). *)


Definition test_prop_DeleteValid (tk: Tree * Z)  :=  
  let '(t, k) := tk in
  prop_DeleteValid t k.

Definition test_prop_DeleteValid_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteValid.

(*! FuzzChick test_prop_DeleteValid (test_prop_DeleteValid_fuzzer tt). *)


Definition test_prop_InsertPost (tkkpv: Tree * Z * Z * Z) :=  
  let '(t, k, k', v) := tkkpv in
  prop_InsertPost t k k' v.

Definition test_prop_InsertPost_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertPost.

(*! FuzzChick test_prop_InsertPost (test_prop_InsertPost_fuzzer tt). *)


Definition test_prop_DeletePost (tkkp: Tree * Z * Z) :=  
  let '(t, k, k') := tkkp in
  prop_DeletePost t k k.

Definition test_prop_DeletePost_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeletePost.

(*! FuzzChick test_prop_DeletePost (test_prop_DeletePost_fuzzer tt). *)
    

Definition test_prop_InsertModel (tkv: Tree * Z * Z)  :=
  let '(t, k, v) := tkv in
  prop_InsertModel t k v.

Definition test_prop_InsertModel_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertModel.

(*! FuzzChick test_prop_InsertModel (test_prop_InsertModel_fuzzer tt). *)
    
Definition test_prop_DeleteModel (tk: Tree * Z)  :=  
  let '(t, k) := tk in
  prop_DeleteModel t k.

Definition test_prop_DeleteModel_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteModel.

(*! FuzzChick test_prop_DeleteModel (test_prop_DeleteModel_fuzzer tt). *)

Definition test_prop_InsertInsert (tkkpvvp: Tree * Z * Z * Z * Z)   :=  
  let '(t, k, k', v, v') := tkkpvvp in
  prop_InsertInsert t k k' v v.

Definition test_prop_InsertInsert_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertInsert.

(*! FuzzChick test_prop_InsertInsert (test_prop_InsertInsert_fuzzer tt). *)
    
Definition test_prop_InsertDelete (tkkpv: Tree * Z * Z * Z)  :=  
  let '(t, k, k', v) := tkkpv in
  prop_InsertDelete t k k' v.

Definition test_prop_InsertDelete_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_InsertDelete.

(*! FuzzChick test_prop_InsertDelete (test_prop_InsertDelete_fuzzer tt). *)
    
Definition test_prop_DeleteInsert (tkkpvp: Tree * Z * Z * Z) :=  
  let '(t, k, k', v') := tkkpvp in
  prop_DeleteInsert t k k' v'.

Definition test_prop_DeleteInsert_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteInsert.

(*! FuzzChick test_prop_DeleteInsert (test_prop_DeleteInsert_fuzzer tt). *)
    
Definition test_prop_DeleteDelete (tkkp: Tree * Z * Z) :=  
  let '(t, k, k') := tkkp in
  prop_DeleteDelete t k k'.

Definition test_prop_DeleteDelete_fuzzer :=
  fun (u : unit) => fuzzLoopWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) arbitrary fuzz show test_prop_DeleteDelete.

(*! FuzzChick test_prop_DeleteDelete (test_prop_DeleteDelete_fuzzer tt). *)
