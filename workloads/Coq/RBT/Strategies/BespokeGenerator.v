


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

Fixpoint genTree (lo hi : Z) (c : Color)  (f: nat) (h : nat) : G (option Tree) 
:=
if lo >? hi then ret None else
match f with
| S f' =>
  match h, c with
  | O, R => ret (Some E)
  | O, B => oneOf [ ret (Some E)
                        ; k <- choose (lo, hi) ;;
                          v <- arbitrary ;;
                          ret (Some (T R E k v E))]
  | S h', R =>
      let margin := (2^(2*(Z.of_nat h) - 1) - 1) in
      if (lo + margin >? hi - margin) then  ret None else
      c' <- ret B ;;
      k <- choose (lo + margin, hi - margin) ;;
      v <- arbitrary ;;
      l <- genTree lo (k - 1)  B f' h' ;;
      r <- genTree (k + 1) hi  B f' h' ;;
       match l, r with
      | Some tl, Some tr => ret (Some (T c' tl k v tr))
      | _, _ => ret None
      end
          
  | S h', B =>
      let margin := (2^(2*(Z.of_nat h)) - 1) in
      if (lo + margin >? hi - margin) then ret None else
      c' <- arbitrary ;;
      k <- choose (lo + margin, hi - margin) ;;
      v <- arbitrary ;;
      let h'' := match c' with R => h | B => h' end in
      l <- genTree lo (k - 1) c' f' h'' ;;
      r <- genTree (k + 1) hi c' f' h'' ;;
      match l, r with
      | Some tl, Some tr => ret (Some (T c' tl k v tr))
      | _, _ => ret None
      end
  end
| _ => ret None
end.

Axiom fuel : nat. Extract Constant fuel => "10000".

Global Instance genTreeSized : GenSized (option Tree) :=
{| arbitrarySized x := 
    let y := Nat.min x 2 in
      genTree 0 (2^(Z.of_nat(y)*2)) R fuel y |}.


Definition gSized := 
    x <- choose (0, 3)%nat;;
    genTree 0 (2^(Z.of_nat(x)*2)) R fuel x
.

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        (prop_InsertValid t k v)))).

(*! QuickChick test_prop_InsertValid. *)

Definition test_prop_DeleteValid :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
        prop_DeleteValid t k)).

(*! QuickChick test_prop_DeleteValid. *)

Definition test_prop_InsertPost :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
     forAll arbitrary (fun v =>
        prop_InsertPost t k k' v)))).

(*! QuickChick test_prop_InsertPost. *)

Definition test_prop_DeletePost := 
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeletePost t k k'))).

(*! QuickChick test_prop_DeletePost. *)
    
Definition test_prop_InsertModel :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun v =>
        prop_InsertModel t k v))).

(*! QuickChick test_prop_InsertModel. *)
    
Definition test_prop_DeleteModel :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
            prop_DeleteModel t k)).

(*! QuickChick test_prop_DeleteModel. *)

Definition test_prop_InsertInsert :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
    forAll arbitrary (fun v' =>     
        prop_InsertInsert t k k' v v'))))).

(*! QuickChick test_prop_InsertInsert. *)
    
Definition test_prop_InsertDelete := 
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v =>
        prop_InsertDelete t k k' v)))).

(*! QuickChick test_prop_InsertDelete. *)
    
Definition test_prop_DeleteInsert := 
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
    forAll arbitrary (fun v' =>
        prop_DeleteInsert t k k' v')))).

(*! QuickChick test_prop_DeleteInsert. *)
    
Definition test_prop_DeleteDelete :=  
    forAllMaybe gSized (fun t =>    
    forAll arbitrary (fun k =>
    forAll arbitrary (fun k' =>
        prop_DeleteDelete t k k'))).

(*! QuickChick test_prop_DeleteDelete. *)
