


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBTProplang Require Import Impl Spec.
From PropLang Require Import PropLang.

Local Open Scope prop_scope.
Open Scope Z_scope.

Derive (Shrink) for Tree.
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
    
#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.
    

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertValid t k v, 0))))).

Definition test_prop_InsertValid_runner := (runLoop number_of_trials test_prop_InsertValid).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0)))).

Definition test_prop_DeleteValid_runner := (runLoop number_of_trials test_prop_DeleteValid).

(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (runLoop number_of_trials test_prop_InsertPost).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (runLoop number_of_trials test_prop_DeletePost).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_InsertModel    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v'" (fun '(v, (t, tt)) => arbitrary) (fun '(v, (t, tt)) n => (fun n => arbitrary)) (fun '(v, (t, tt)) n => shrink n) (fun '(v, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

    
Definition test_prop_InsertModel_runner := (runLoop number_of_trials test_prop_InsertModel).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

    
Definition test_prop_DeleteModel_runner := (runLoop number_of_trials test_prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (Z · (Z · (Z · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (Z · (Z · (Z · (Z · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (runLoop number_of_trials test_prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (runLoop number_of_trials test_prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete_runner. *)


Definition test_prop_DeleteInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (runLoop number_of_trials test_prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => bespoke)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => genZ) (fun '(t, tt) n => (fun n => genZ)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => genZ) (fun '(k, (t, tt)) n => (fun n => genZ)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (runLoop number_of_trials test_prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete_runner. *)