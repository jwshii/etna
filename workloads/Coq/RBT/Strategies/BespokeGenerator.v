


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.


From RBT Require Import Impl Spec.

Open Scope Z_scope.

Definition genZ := choose (-20, 20).

Fixpoint gen_kvs (s : nat) : G (list (Z * Z)) :=
  match s with
  | O => ret []
  | S s' => k <- genZ;;
           v <- arbitrary;;
           kvs <- gen_kvs s';;
           ret ((k, v) :: kvs)
  end.

Definition blacken_ (t: Tree) : Tree :=
    match t with
    | E => E
    | (T _ a x vx b) => T B a x vx b
    end.

Definition balance_ (col: Color) (tl: Tree) (key: Z) (val: Z) (tr: Tree) : Tree :=
    match col, tl, key, val, tr with
    | B, (T R (T R a x vx b) y vy c), z, vz, d => T R (T B a x vx b) y vy (T B c z vz d)
    | B, (T R a x vx (T R b y vy c)), z, vz, d => T R (T B a x vx b) y vy (T B c z vz d)
    | B, a, x, vx, (T R (T R b y vy c) z vz d) => T R (T B a x vx b) y vy (T B c z vz d)
    | B, a, x, vx, (T R b y vy (T R c z vz d)) => T R (T B a x vx b) y vy (T B c z vz d)
    | rb, a, x, vx, b => T rb a x vx b
    end.


Fixpoint insert_ (key: Z) (val: Z) (t: Tree) : Tree :=
    let fix ins (x: Z) (vx: Z) (s: Tree) : Tree :=
    match x, vx, s with
    | x, vx, E => 
    T R E x vx E
    | x, vx, (T rb a y vy b) =>
    if x <?? y then balance_ rb (ins x vx a) y vy b
    else if y <?? x then balance_ rb a y vy (ins x vx b)
    else T rb a y vx b
    end
    in blacken_ (ins key val t).

Definition gen_tree (s : nat) : G Tree :=
    sz <- choose(1, s)%nat;;
    kvs <- gen_kvs sz;;
    ret (fold_right (fun '(k, v) t => insert_ k v t) E kvs).

Definition bespoke :=
    gen_tree 20.
    
(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)


Definition test_prop_InsertPost :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)

Definition test_prop_DeleteInsert := 
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
    forAll arbitrary (fun v' =>
    (prop_DeleteInsert t k k' v'))))).

(*! QuickChick test_prop_DeleteInsert. *)

Definition test_prop_DeleteDelete :=  
    forAll bespoke (fun t =>    
    forAll genZ (fun k =>
    forAll genZ (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)
