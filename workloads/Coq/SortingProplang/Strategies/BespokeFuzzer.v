
From QuickChick Require Import QuickChick. Import QcDefaultNotation.
From ExtLib Require Import Monad. Import MonadNotation.

Require Import List. Import ListNotations.
Require Import Nat.

From PropLang Require Import PropLang.
From SortingProplang Require Import Impl.

Open Scope qc_scope.
Open Scope list.
Open Scope prop_scope.

Derive Arbitrary for list.

Fixpoint substList {A: Type} (l : list A) (i : nat) (j : nat) (l' : list A) : list A :=
  match l with
  | [] => []
  | h :: t => if i =? 0 then 
                if j =? 0 then l' ++ (h :: t)
                else substList t 0 (j - 1) l'
              else h :: substList t (i - 1) (j - 1) l'
  end.


  
Definition listOf (n : nat) {A: Type} `{Gen A} : G (list A) :=
  let fix listOf' (n : nat) (l : list A) : G (list A) :=
    match n with
    | O => ret l
    | S n' => x <- arbitrary ;;
              listOf' n' (x :: l)
    end in
  listOf' n [].

Definition chooseIndex (l : list nat) (i: nat) : G nat :=
  choose (i, length l).


#[local] Instance genList : Gen (list nat) :=
  {|
    arbitrary := listOf 100;
  |}.
  
  
#[local] Instance fuzzListNat : Fuzzy (list nat) :=
{|
  fuzz := fun l => freq [
                  (* replace part of a list *) 
                  (10,
                    i <- chooseIndex l 0 ;;
                    j <- chooseIndex l i ;;
                    let len := j - i in
                    bindGen (listOf len) (fun l' => ret (substList l i j l'))
                  );
                  (* prepend list with a new generated list *)
                  (* (1,
                    l' <- arbitrary ;;
                    ret (l' ++ l)
                  ); *)
                  (* append list with a new generated list *)
                  (* (1,
                    l' <- arbitrary ;;
                    ret (l ++ l')
                  ); *)
                  (* insert list with a new generated list *)
                  (* (1,
                    l' <- arbitrary ;;
                    i <- chooseIndex l 0 ;;
                    ret (substList l i i l')
                  ); *)
                  (* remove some part of the list *)
                  (3,
                    i <- chooseIndex l 0 ;;
                    j <- chooseIndex l i ;;
                    ret (substList l i j [])
                  )
                  ]
|}.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "100".

Axiom sorted : (list nat) -> bool.
Extract Constant sorted => "fun l -> true".

Definition prop_sort : CProp ∅ :=
  @ForAll _ ∅ "l" (fun _ => arbitrary) (fun _ => fuzz) (fun _ n => shrink n) (fun _ n => show n) (
  @Check (list nat · ∅)
              (fun '(l, _) =>
                let l := sort l in sorted l)).


Definition test_prop_sort := (perfFuzzLoop number_of_trials prop_sort (HeapSeedPool.(mkPool) tt) HillClimbingUtility).
(*! QuickProp test_prop_sort. *)