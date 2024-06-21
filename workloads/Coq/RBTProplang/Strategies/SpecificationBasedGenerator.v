


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

Definition prop_InsertValid :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => (isRBT (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).
(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Tree · ∅))
	(fun '(k, (t, _)) => (match delete k t with
						   | None => false
						   | Some t' => isRBT t'
							end))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).
(*! QuickProp test_prop_DeleteValid. *)

Definition prop_InsertPost :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => (let v' := find k' (insert k v t) in
										if k =? k' then (v' = Some v)?
										else (v' = find k' t)?))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).
(*! QuickProp test_prop_InsertPost. *)

Definition prop_DeletePost :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => (match delete k t with
								| None => false
								| Some t' =>
								(find k' t' = if k =? k' then None else find k' t)?
								end)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)


Definition prop_InsertModel :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(v, (k, (t, _))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Tree · ∅))
	(fun '(k, (t, _)) => ( match delete k t with
							| None => false
							| Some t' => (toList t' = deleteKey k (toList t))?
							end))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_InsertInsert :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v' => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Z · (Z · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, _))))) => (
		(toList (insert k v (insert k' v' t)) = toList(if k =? k' then insert k v t else insert k' v' (insert k v t)))?
	)))))))).


Definition test_prop_InsertInsert := (runLoop number_of_trials prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert. *)


Definition prop_InsertDelete :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ k => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ k' => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v, (k', (k, (t, _)))) => (
		match (delete k' t) with
		| None => false
		| Some t' =>
			match delete k' (insert k v t) with
			| None => false
			| Some t'' =>
				(toList(insert k v t') = toList(if k =? k' then insert k v t else t''))?
			end
		end))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_DeleteInsert :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "v'" (fun _ => arbitrary) (fun _ v => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v', (k', (k, (t, _)))) => (
		match delete k (insert k' v' t) with
		| None => false
		| Some t' =>
			match delete k t with
			| None => false
			| Some t'' =>
				let t''' := insert k' v' t'' in
				(toList t' = toList (if k =? k' then t'' else t'''))?
			end
		end
	))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAllMaybe "t" (fun _ => gRbt) (fun _ t => gRbt) (fun _ => shrink) (fun _ => show) (
	Implies (Tree · ∅) (fun '(t, _) => isRBT t) (
	ForAll "k" (fun _ => arbitrary) (fun _ t => arbitrary) (fun _ => shrink) (fun _ => show) (
	ForAll "k'" (fun _ => arbitrary) (fun _ n => arbitrary) (fun _ => shrink) (fun _ => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(k', (k, (t, _))) => (
		match delete k' t with
		| None => false
		| Some t' =>
			match delete k t' with
			| None => false
			| Some t'' =>
				match delete k t with
				| None => false
				| Some t1' =>
					match delete k' t1' with
					| None => false
					| Some t1'' =>
						(toList t'' = toList t1'')?
					end
				end
			end
		end
	)))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)