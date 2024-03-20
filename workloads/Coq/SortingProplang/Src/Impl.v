
Require Import List.
Import ListNotations.

Require Import Nat.
Local Open Scope nat.
Local Open Scope nat_scope.

Require Import Bool.
Import BoolNotations.

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if Nat.leb i h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.
