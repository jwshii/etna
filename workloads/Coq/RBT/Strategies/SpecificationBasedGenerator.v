
Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.


From RBT Require Import Impl Spec.



Local Open Scope Z_scope.


Inductive between : Z -> Z -> Z -> Prop :=
| between_n : forall n m, Z.le n m -> between n (n + 1) (m + 2)
| between_S : forall n m o, between n m o -> between n (m + 1) (o + 1).

Inductive red_black_bst : Color -> nat -> Z -> Z -> Tree -> Prop :=
    rbt_leafbh_leafbst_leaf : forall (lo hi : Z) (c : Color),
                              red_black_bst c 1 lo hi E
  | rbt_black_nodebh_black_nodebst_node : forall (lo hi x y: Z)
                                            (l r : Tree) (h : nat)
                                            (c1 c2 : Color),
                                          between lo x hi ->
                                          red_black_bst c1 h lo x l ->
                                          red_black_bst c2 h x hi r ->
                                          red_black_bst B (S h) lo hi (T B l x y r)
  | rbt_red_nodebh_red_nodebst_node : forall (lo hi x y: Z) (l r : Tree) (h : nat),
                                      between lo x hi ->
                                      red_black_bst B h lo x l ->
                                      red_black_bst B h x hi r ->
                                      red_black_bst R h lo hi (T R l x y r).


#[local] Instance gen_between (lo hi : Z) :
GenSizedSuchThat _ (fun x => between lo x hi) :=
{| arbitrarySizeST := fun n =>
                        if Z.leb 2 (hi - lo) then
                          bindGen (choose (lo+1,hi-1)%Z) (fun x => ret (Some x))
                        else ret None
|}%nat.

Derive ArbitrarySizedSuchThat for (fun t => red_black_bst c h lo hi t).

Definition gRbt := 
    (@arbitrarySizeST _ (fun t => red_black_bst B 3 0 100 t) _ 10).

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAllMaybe gRbt (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)
