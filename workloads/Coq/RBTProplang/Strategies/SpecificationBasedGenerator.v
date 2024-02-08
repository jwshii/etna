


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBTProplang Require Import Impl Spec PropLang.

Local Open Scope prop_scope.
Open Scope Z_scope.

Derive (Shrink) for Tree.



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

    
#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.
    

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition test_prop_InsertValid   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertValid t k v, 0))))).

Definition test_prop_InsertValid_runner := (runLoop number_of_trials test_prop_InsertValid).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0)))).

Definition test_prop_DeleteValid_runner := (runLoop number_of_trials test_prop_DeleteValid).

(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (runLoop number_of_trials test_prop_InsertPost).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (runLoop number_of_trials test_prop_DeletePost).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_InsertModel    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "v'" (fun '(v, (t, tt)) => arbitrary) (fun '(v, (t, tt)) n => (fun n => arbitrary)) (fun '(v, (t, tt)) n => shrink n) (fun '(v, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

    
Definition test_prop_InsertModel_runner := (runLoop number_of_trials test_prop_InsertModel).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Z · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

    
Definition test_prop_DeleteModel_runner := (runLoop number_of_trials test_prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (Z · (Z · (Z · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (Z · (Z · (Z · (Z · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (runLoop number_of_trials test_prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (runLoop number_of_trials test_prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete_runner. *)


Definition test_prop_DeleteInsert    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (Z · (Z · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (Z · (Z · (Z · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (runLoop number_of_trials test_prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAllMaybe _ ∅ _ "t" (fun tt => gRbt) (fun tt n => (fun n => gRbt)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Z · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (Z · (Z · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (runLoop number_of_trials test_prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete_runner. *)