From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Inductive Ctx :=
| EmptyCtx
| CtxBind : Type -> Ctx -> Ctx.

Declare Scope prop_scope.
Notation "'∅'" := EmptyCtx : prop_scope.
Notation " A '·' C " :=
  (CtxBind A C) (at level 70) : prop_scope.

Local Open Scope prop_scope.

Fixpoint interpCtx (C : Ctx) : Type :=
  match C with
  | ∅ => unit
  | T·C => T * interpCtx C
  end.

Notation "'⟦' C '⟧'" := (interpCtx C) : prop_scope.

Inductive CProp : Ctx -> Type -> Type :=
| ForAll : forall A C F
      (name: string)
      (generator : ⟦C⟧ -> G A)
      (mutator   : ⟦C⟧ -> nat -> A -> G A)
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) F -> CProp C F
  | Predicate : forall C F,
      (⟦C⟧ -> option bool * F) -> CProp C F.

Fixpoint inputTypes {C : Ctx} {F : Type}
         (cprop : CProp C F) : Ctx :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | Predicate _ _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@inputTypes _ _ c).

Definition typeHead {C : Ctx} {F : Type}
         (cprop : CProp C F) : Type :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' => A
  | Predicate _ _ _ => unit
  end.


Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition mut (k n : nat) : G nat :=
  choose (n - k, n + k).
Definition test (x y : nat) : option bool :=
  Some (Nat.ltb y x).

Local Open Scope string.

Definition example :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) unit
             (fun '(y, (x, tt)) => (test x y, tt)))).

Fixpoint genAndRun {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (⟦⦗cprop⦘⟧ * (option bool * F)) :=
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        res <- genAndRun cprop' (a,env);;
        let '(env', (truth, feedback)) := res in
        ret ((a,env'), (truth, feedback))
  | Predicate C F prop =>
      fun env => returnGen (tt, prop env)
  end.

Fixpoint justGen {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (⟦⦗cprop⦘⟧) :=
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        env <- justGen cprop' (a,env);;
        ret (a,env)
  | Predicate C F prop =>
      fun env => ret tt
  end.

Fixpoint mutAll {C : Ctx} {F : Type}
         (cprop : CProp C F) (t: nat)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)) :=
  match cprop with
  | ForAll A C F name gen mut shr pri cprop' =>
      fun env '(x,xs) =>
        x' <- mut env t x;;
        xs' <- mutAll cprop' t (x', env) xs;;
        ret (x', xs')
  | Predicate C F prop =>
      fun _ _ => ret tt
  end.

Fixpoint mutSome {C : Ctx} {F : Type}
  (cprop : CProp C F) (t: nat)
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)) :=
  match cprop with
  | ForAll A C F name gen mut shr pri cprop' =>
    fun env '(x,xs) =>
    mut_oracle <- choose (0, 1);;
    x' <- mut env t x;;
    xs' <- mutSome cprop' t (x', env) xs;;
    match mut_oracle with
    | 0 => ret (x', xs')
    | _ => ret (x, xs')
    end
  | Predicate C F prop =>
  fun _ _ => ret tt
end.

Fixpoint print {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string) :=
  match cprop with
  | ForAll A C F name gen mut shr pr cprop' =>
      fun env '(a,inps') =>
        (name, pr env a) :: (print cprop' (a, env) inps')
  | Predicate C F prop =>
      fun _ _ => nil
  end.

Fixpoint showElemList (l: list (string * string)) : string :=
  match l with
  | [] => ""
  | ((k, v) :: []) => (k ++ ": " ++ v) 
  | ((k, v) :: t) => (k ++ ": " ++ v ++ ", " ++ showElemList t)
  end.

Local Open Scope Z.

Record Seed {A F: Type} := {
  input: A;
  feedback: F;
  energy: Z;
}.

Definition mkSeed {A F: Type} (a: A) (f: F) (e: Z): Seed := {| input := a; feedback := f; energy := e |}.

Definition Temperature := Z.

Inductive Directive {A F: Type} :=
| Generate : Directive
| Mutate : @Seed A F -> Temperature -> Directive
.

#[global] Instance showDirective {A F: Type} : Show (@Directive A F) :=
{|
  show d := match d with
            | Generate => "Generate"
            | Mutate _ t => "Mutate(" ++ show t ++ ")"
            end
|}.


Class SeedPool {A F Pool: Type} := {
  (* Creates an empty pool. *)
  mkPool  : unit -> Pool;
  (* Adds a useful seed into the pool. *)
  invest  : (A * F) -> Pool -> Pool;
  (* Decreases the energy of a seed after a useless trial. *)
  revise  : Pool -> A -> (A * F) -> Pool;
  (* Samples the pool for an input. *)
  sample  : Pool -> @Directive A F;
  (* Returns the best seed in the pool. *)
  best    : Pool -> option (@Seed A F);
}.



Class Utility {A F Pool: Type} `{SeedPool A F Pool} := {
  (* Returns true if the feedback is interesting. *)
  useful  : Pool -> F -> bool;
  (* Returns a metric of how interesting the feedback is. *)
  utility : Pool -> F -> Z;
}.

Class Scalar (A : Type) :=
  { scale : A -> Z }.

#[global] Instance ScalarZ : Scalar Z :=
  {| scale := fun x => x |}.


(* Class Scheduler {A F Pool: Type} `{SeedPool A F Pool} := {
  invest  : (A * F) -> Pool -> Pool;
  revise  : Pool -> A -> (A * F) -> Pool;
}. *)

Record SingletonPool {A F: Type} := {
  seed: option (@Seed A F);
}.

#[global] Instance StaticSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
     invest seed pool := match seed with 
                         | (a, f) => {| seed := Some (mkSeed a f 1) |}
                         end ;
     revise pool a _ := pool ;
     sample pool := match seed pool with
                    | None => Generate
                    | Some seed => Mutate seed 1
                    end ;
     best pool := seed pool
  |}.

#[global] Instance DynamicMonotonicSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 20) |}
                        end ;
    revise pool a _ := match seed pool with
                       | None => pool
                       | Some seed => 
                        let a' := input seed in
                        let f := feedback seed in
                        let n := energy seed in
                        if (a = a')? then {| seed := Some (mkSeed a f (n - 1)) |} else pool
                        end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else if (energy seed >? 12) then Mutate seed (energy seed - 12)
                                    else Mutate seed (13 - energy seed)

                   end ;
    best pool := seed pool
|}.

#[global] Instance DynamicResettingSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 100) |}
                        end ;
    revise pool a _ := match seed pool with
                       | None => pool
                       | Some seed => 
                        let a' := input seed in
                        let f := feedback seed in
                        let n := energy seed in
                        if (a = a')? then {| seed := Some (mkSeed a f (n - 1)) |} else pool
                        end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else if (energy seed >=? 96) then Mutate seed (energy seed - 50)
                                    else Mutate seed (100 - energy seed)
                   end ;
    best pool := match seed pool with
                 | None => None
                 | Some seed => if (energy seed =? 0) then None else Some seed
                 end
|}.


#[global] Instance HillClimbingUtility {A F Pool} `{SeedPool A F Pool} `{Scalar F} 
: Utility := 
{|
  useful  := fun pool feedback' => match best pool with
                                  | None => true
                                  | Some seed => (scale feedback') >? (scale (feedback seed))
                                  end;
  utility := fun pool feedback' => match best pool with
                                  | None => scale feedback'
                                  | Some seed => scale feedback' - (scale (feedback seed))
                                  end
|}.

(* 
Record DoubleQueuePool {A E : Type} := {
  hpq: list (A * E);
  lpq: list (A * E);
}.

Definition insertHighPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (seed :: (hpq pool)) ; lpq := (lpq pool) |}.

Definition insertLowPrioritySeed {A E: Type} (seed: (A * E)) (pool: DoubleQueuePool) : DoubleQueuePool :=
  {| hpq := (hpq pool) ; lpq := (seed :: (lpq pool)) |} .

Fixpoint maxSeed {A E: Type} `{OrdType E} (cmax: option (A * E)) (q: list (A * E)) : option A :=
  match q with
  | [] => match cmax with
          | None => None
          | Some (a, e) => Some a
          end
  | (h :: t) => match cmax with
                | None => maxSeed (Some h) t
                | Some (a, e) => if leq e (snd h) then maxSeed (Some h) t else maxSeed (Some (a, e)) t
                end
  end.

Definition sampleSeedDQP {A E : Type} `{OrdType E} (pool: DoubleQueuePool) : option A * DoubleQueuePool :=
  match (hpq pool) with
  | []  => (maxSeed None (lpq pool), pool)
  | _   => (maxSeed None (hpq pool), pool)
  end.


  #[global] Instance SeedPoolDQP {A E : Type} `{OrdType E} : @SeedPool A E (@DoubleQueuePool A E) :=
  {| mkPool _ := {| hpq := []; lpq := [] |};
     schedule pool seed := pool;
     insert seed pool := {| hpq := seed :: (hpq pool); lpq := lpq pool |};
     sample pool :=
       match (hpq pool) with
       | []  => (maxSeed None (lpq pool), pool)
       | _   => (maxSeed None (hpq pool), pool)
       end
  |}. *)



Fixpoint runAndTest {C:Ctx} {F : Type} (cprop : CProp C F)
         (cenv : ⟦C⟧)
         (fenv :  ⟦⦗cprop⦘⟧)
         {struct cprop}
  : option bool * F.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv'] eqn:H.
    apply IHcprop.
    + exact (a, cenv).
    + exact fenv'.
  - exact (p cenv).
Defined.


Fixpoint shrinkOnTheFly
  {C : Ctx} {F: Type}
  (cprop : CProp C F)
  (cenv :  ⟦C⟧)
  (fenv :  ⟦⦗cprop⦘⟧)
  {struct cprop}
  : option ⟦⦗cprop⦘⟧.
Proof.
  induction cprop; simpl in *.
  - destruct fenv as [a fenv']. 
    (* Recurse through the list of shrinks *)
    induction (shrinker cenv a).
    (* No more shrinks - try the next element of the property *)
    + destruct (shrinkOnTheFly _ _ cprop (a,cenv) fenv') eqn:M.
      * exact (Some (a, i)).
      * exact None.
    (* More shrinks - run the property on the shrunk possibility. *)
    + destruct (runAndTest cprop (a0,cenv) fenv') eqn:T. destruct o.
      * destruct b.
        (* Test succeeded - recurse down the list. *)
        -- apply IHl.
        (* Test failed - end with current result. *)
        -- exact (Some (a0, fenv')).     
      * (* Test discarded - recurse down the list. *)
        apply IHl.
  - exact None.
Defined.

Fixpoint shrinkLoop {F: Type} (fuel : nat)
  (cprop: CProp ∅ F) (counterexample : ⟦⦗cprop⦘⟧) :
  ⟦⦗cprop⦘⟧ :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrinkOnTheFly cprop tt counterexample with
      | Some c' => shrinkLoop fuel' cprop c'
      | None => counterexample
      end
  end.

Definition generator (cprop: CProp ∅ Z) (directive: @Directive ⟦⦗cprop⦘⟧ Z) :=
  match directive with
  | Generate => justGen cprop tt
  | Mutate seed t => mutAll cprop (Z.to_nat t) tt (input seed)
  end.


Fixpoint runLoop (fuel : nat)
  (cprop : CProp ∅ Z)
: G (list (string * string)) :=
match fuel with
| O => ret []
| S fuel' => 
seed <- justGen cprop tt;;
let res := runAndTest cprop tt seed in
let '(truth, feedback) := res in
  match truth with
  | Some false =>
    (* Fails *)
    let shrinkingResult := shrinkLoop 10 cprop seed in
    let printingResult := print cprop tt shrinkingResult in
    ret (("tests to failure", show (200000%nat - fuel)%nat) :: printingResult)
  | Some true =>
    (* Passes *)
    runLoop fuel' cprop
  | None => 
    (* Discard *)
    runLoop fuel' cprop
  end
end.

  
Fixpoint targetLoop (fuel : nat)
         (cprop : CProp ∅ Z)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility)
  : G (list (string * string)) :=
  match fuel with
  | O => ret []
  | S fuel' => 
      let directive := sample seeds in
      seed <- generator cprop directive;;
      let res := runAndTest cprop tt seed in
      let '(truth, feedback) := res in
      match truth with
      | Some false =>
          (* Fails *)
          let shrinkingResult := shrinkLoop 10 cprop seed in
          let printingResult := print cprop tt shrinkingResult in
          ret printingResult
      | Some true =>
          (* Passes *)
          match useful seeds feedback with
          | true =>
              let seeds' := invest (seed, feedback) seeds in
              targetLoop fuel' cprop seeds' poolType utility
          | false =>
              let seeds' := match directive with
                            | Generate => seeds
                            | Mutate source _ => revise seeds (input source) (seed, feedback)
                            end in
              targetLoop fuel' cprop seeds' poolType utility
          end
      | None => 
          (* Discard *)
          targetLoop fuel' cprop seeds poolType utility
      end
  end.

Definition test2 (x y : nat) : option bool :=
  Some (negb (Nat.eqb y  x)).


Definition example2 :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
              (fun '(y, (x, tt)) => (test2 x y, 0)))).

Definition example3 :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
              (fun '(y, (x, tt)) => (test2 x y, (2000 - Z.of_nat(x - y) - Z.of_nat(y - x)))))).
  
Definition example3' :=
  forAll arb (fun (x: nat)  =>
  forAll (gen x) (fun (y: nat)  =>
  test2 x y)).


#[local] Instance showUnit : Show unit :=
  {| show _ := "()" |}.

(* Check example3. *)
(* Check toMonad example3 (3, (2, tt)). *)
Fixpoint toMonad {C : Ctx} {F: Type} (cprop: CProp C F) : ⟦C⟧ -> Checker :=
  match cprop with
  | ForAll A C F name gen mut shr pri cprop' =>
    fun env =>
      forAllShrinkShow (gen env) (shr env) (pri env) (fun a => toMonad cprop' (a, env))
  | Predicate C F prop =>
    fun env => 
      forAll (returnGen tt) (fun _ => match prop env with
                                      | (Some true, _) => returnGen true
                                      | _ => returnGen false
                                      end)
  end.

Definition example3'' := toMonad example3.

(* Sample (targetLoop 1000 example2 (mkPool tt) StaticSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example2 (mkPool tt) DynamicSingletonPool HillClimbingUtility).
Sample (targetLoop 1000 example3 (mkPool tt) DynamicSingletonPool HillClimbingUtility). *)


Definition Log := list (string).

Definition printSeed (cprop : CProp ∅ Z ) (seed: @Seed ⟦⦗cprop⦘⟧ Z) : string :=
   showElemList (print cprop tt (input seed)) ++ ", feedback: " ++ show (feedback seed) ++ ", energy: " ++ show (energy seed).

#[local] Instance showListNL {A: Type} `{Show A} : Show (list A) :=
  {| show l := String.concat nl (map show l) |}.


Fixpoint targetLoopLogged (fuel : nat)
         (cprop : CProp ∅ Z)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility)
         (log   : Log)
  : G Log :=
  match fuel with
  | O => ret (rev log)
  | S fuel' => 
      let directive := sample seeds in
      seed <- generator cprop directive;;
      let res := runAndTest cprop tt seed in
      let '(truth, feedback) := res in
      let printedSeed := showElemList (print cprop tt seed) in
      
      let printedSource := match directive with 
                           | Generate => "None"
                           | Mutate seed _ => printSeed cprop seed
                           end in
      let log := ("source: [" ++ printedSource ++ "], seed: [" ++ printedSeed ++ ", feedback: " ++ show feedback ++ "], truth: " ++ show truth ++ ", fuel: " ++ show fuel ++ ", directive:" ++ show directive) :: log in
      match truth with
      | Some false =>
          (* Fails *)
          ret (rev log)
      | Some true =>
          (* Passes *)
          match useful seeds feedback with
          | true =>
              let seeds' := invest (seed, feedback) seeds in
              targetLoopLogged fuel' cprop seeds' poolType utility log
          | false =>
              let seeds' := match directive with
                          | Generate => seeds
                          | Mutate source _ => revise seeds (input source) (seed, feedback)
                          end in
              targetLoopLogged fuel' cprop seeds' poolType utility log
          end
      | None => 
          (* Discard *)
          targetLoopLogged fuel' cprop seeds poolType utility log
      end
  end.

Definition bench_qc := forAll (choose (0, 1000)) (fun tt  => ret (Some true)).
Definition bench_prl := 
  @ForAll _ ∅ _ "x" (fun tt => (choose (0, 1000)%nat)) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · ∅) Z
              (fun '(x, tt) => (Some true, 0))).

Definition bench_prl_function := (targetLoop 100000 bench_prl (mkPool tt) StaticSingletonPool HillClimbingUtility).
Definition bench_transformed := toMonad bench_prl tt.
Definition qctest_bench_qc := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (quickCheckWith (updMaxSuccess (updAnalysis stdArgs true) 100000) bench_qc))) ++ "}|]")).
Definition qctest_bench_prl := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 bench_prl_function))) ++ "}|]")).


Definition qctest_bench_transformed := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (quickCheckWith (updMaxSuccess (updAnalysis stdArgs true) 100000) bench_transformed))) ++ "}|]")).

Extraction "bench.ml" qctest_bench_qc qctest_bench_prl qctest_bench_transformed.

(* Sample1 (targetLoopLogged 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility nil).
Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility nil).
Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)

(* Sample1 (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility).
Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility).
Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility). *)

From BST Require Import Impl.
From BST Require Import Spec.

Local Open Scope nat.

Fixpoint gen_bst (s : nat) (lo hi : nat) : G Tree :=
  match s with
  | O => ret E
  | S s' => freq [(1, ret E)
                 ;(if hi - lo < 2? then 0 else s,
                    k <- choose (lo+1, hi-1);;
                    v <- arbitrary;;
                    l <- gen_bst s' lo k;;
                    r <- gen_bst s' k hi;;
                    ret (T l k v r))]
  end.

Fixpoint mutate_bst (t : Tree) : G Tree :=
  match t with
  | E => freq [(4, ret E)
              ;(1, gen_bst 1 0 10)]
  | T l k v r => freq [
    (1, ret t);
    (3, l' <- mutate_bst l;; ret (T l' k v r));
    (3, r' <- mutate_bst r;; ret (T l k v r'));
    (1, k' <- choose (k-1, k+1);;
        ret (T l k' v r));
    (1, v' <- arbitrary;;
        ret (T l k v' r))]
  end.

#[local] Instance shrinkTree : Shrink Tree :=
{|
  shrink t := match t with
              | E => []
              | T l k v r => [l; r]
              end
|}.
Definition bespoke := gen_bst 4 0 40.

Derive (Arbitrary, Show) for Tree.

Local Open Scope Z.
(* 
Definition test_prop_InsertPost :=
  @ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => mutate_bst n)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
              (fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))). *)


#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

(* Definition runner := (targetLoopLogged 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)
(* Definition runner := runLoop 200000 test_prop_InsertPost. *)
(* Sample1 runner. *)

(* Definition runner' := (targetLoopLogged 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)
(* Sample1 runner'. *)


Definition test_prop_InsertValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertValid t k v, 0%Z))))).

Definition test_prop_InsertValid_runner := (targetLoop 20000 test_prop_InsertValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).

(*! QuickProp test_prop_InsertValid_runner. *)

Definition test_prop_DeleteValid   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteValid t k, 0%Z)))).

Definition test_prop_DeleteValid_runner := (targetLoop 20000 test_prop_DeleteValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteValid_runner. *)

Definition test_prop_UnionValid    :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => arbitrary)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t2, (t1, tt)) => (prop_UnionValid t1 t2, 0%Z)))).

Definition test_prop_UnionValid_runner := (targetLoop 20000 test_prop_UnionValid (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionValid_runner. *)

Definition test_prop_InsertPost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertPost t k k' v, 0%Z)))))).

Definition test_prop_InsertPost_runner := (targetLoop 20000 test_prop_InsertPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertPost_runner. *)

Definition test_prop_DeletePost    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => (prop_DeletePost t k k', 0%Z))))).

Definition test_prop_DeletePost_runner := (targetLoop 20000 test_prop_DeletePost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeletePost_runner. *)

Definition test_prop_UnionPost   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_UnionPost t t' k, 0%Z))))).

Definition test_prop_UnionPost_runner := (targetLoop 20000 test_prop_UnionPost (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionPost_runner. *)

Definition test_prop_InsertModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "v" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(v, (k, (t, tt))) => (prop_InsertModel t k v, 0%Z))))).

Definition test_prop_InsertModel_runner := (targetLoop 20000 test_prop_InsertModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertModel_runner. *)

Definition test_prop_DeleteModel   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (nat · (Tree · ∅)) Z
	(fun '(k, (t, tt)) => (prop_DeleteModel t k, 0%Z)))).

Definition test_prop_DeleteModel_runner := (targetLoop 20000 test_prop_DeleteModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteModel_runner. *)

Definition test_prop_UnionModel    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@Predicate (Tree · (Tree · ∅)) Z
	(fun '(t', (t, tt)) => (prop_UnionModel t t', 0%Z)))).

Definition test_prop_UnionModel_runner := (targetLoop 20000 test_prop_UnionModel (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionModel_runner. *)

Definition test_prop_InsertInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@ForAll _ (nat · (nat · (nat · (Tree · ∅)))) _ "v'" (fun '(v, (k', (k, (t, tt)))) => arbitrary) (fun '(v, (k', (k, (t, tt)))) n => (fun n => arbitrary)) (fun '(v, (k', (k, (t, tt)))) n => shrink n) (fun '(v, (k', (k, (t, tt)))) n => show n) (
	@Predicate (nat · (nat · (nat · (nat · (Tree · ∅))))) Z
	(fun '(v', (v, (k', (k, (t, tt))))) => (prop_InsertInsert t k k' v v', 0%Z))))))).

Definition test_prop_InsertInsert_runner := (targetLoop 20000 test_prop_InsertInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertInsert_runner. *)

Definition test_prop_InsertDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v, (k', (k, (t, tt)))) => (prop_InsertDelete t k k' v, 0%Z)))))).

Definition test_prop_InsertDelete_runner := (targetLoop 20000 test_prop_InsertDelete (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertDelete_runner. *)

Definition test_prop_InsertUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t, tt))) => arbitrary) (fun '(k, (t', (t, tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t, tt))) n => shrink n) (fun '(k, (t', (t, tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => (prop_InsertUnion t t' k v, 0%Z)))))).

Definition test_prop_InsertUnion_runner := (targetLoop 20000 test_prop_InsertUnion (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_InsertUnion_runner. *)

Definition test_prop_DeleteInsert    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@ForAll _ (nat · (nat · (Tree · ∅))) _ "v'" (fun '(k', (k, (t, tt))) => arbitrary) (fun '(k', (k, (t, tt))) n => (fun n => arbitrary)) (fun '(k', (k, (t, tt))) n => shrink n) (fun '(k', (k, (t, tt))) n => show n) (
	@Predicate (nat · (nat · (nat · (Tree · ∅)))) Z
	(fun '(v', (k', (k, (t, tt)))) => (prop_DeleteInsert t k k' v', 0%Z)))))).

Definition test_prop_DeleteInsert_runner := (targetLoop 20000 test_prop_DeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteInsert_runner. *)

Definition test_prop_DeleteDelete    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "k" (fun '(t, tt) => arbitrary) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (nat · (Tree · ∅)) _ "k'" (fun '(k, (t, tt)) => arbitrary) (fun '(k, (t, tt)) n => (fun n => arbitrary)) (fun '(k, (t, tt)) n => shrink n) (fun '(k, (t, tt)) n => show n) (
	@Predicate (nat · (nat · (Tree · ∅))) Z
	(fun '(k', (k, (t, tt))) => ((prop_DeleteDelete t k k', 0%Z)))))).

Definition test_prop_DeleteDelete_runner := (targetLoop 20000 test_prop_DeleteDelete (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteDelete_runner. *)

Definition test_prop_DeleteUnion   :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t, tt) => bespoke) (fun '(t, tt) n => (fun n => arbitrary)) (fun '(t, tt) n => shrink n) (fun '(t, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t, tt)) => arbitrary) (fun '(t', (t, tt)) n => (fun n => arbitrary)) (fun '(t', (t, tt)) n => shrink n) (fun '(t', (t, tt)) n => show n) (
	@Predicate (nat · (Tree · (Tree · ∅))) Z
	(fun '(k, (t', (t, tt))) => (prop_DeleteUnion t t' k, 0%Z))))).

Definition test_prop_DeleteUnion_runner := (targetLoop 20000 test_prop_DeleteUnion (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_DeleteUnion_runner. *)

Definition test_prop_UnionDeleteInsert   :=
	@ForAll _ ∅ _ "t " (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t'" (fun '(t , tt) => bespoke) (fun '(t , tt) n => (fun n => arbitrary)) (fun '(t , tt) n => shrink n) (fun '(t , tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "k" (fun '(t', (t , tt)) => arbitrary) (fun '(t', (t , tt)) n => (fun n => arbitrary)) (fun '(t', (t , tt)) n => shrink n) (fun '(t', (t , tt)) n => show n) (
	@ForAll _ (nat · (Tree · (Tree · ∅))) _ "v" (fun '(k, (t', (t , tt))) => arbitrary) (fun '(k, (t', (t , tt))) n => (fun n => arbitrary)) (fun '(k, (t', (t , tt))) n => shrink n) (fun '(k, (t', (t , tt))) n => show n) (
	@Predicate (nat · (nat · (Tree · (Tree · ∅)))) Z
	(fun '(v, (k, (t', (t, tt)))) => ((prop_UnionDeleteInsert t t' k v, 0%Z))))))).

Definition test_prop_UnionDeleteInsert_runner := (targetLoop 20000 test_prop_UnionDeleteInsert (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionDeleteInsert_runner. *)

Definition test_prop_UnionUnionIdem    :=
	@ForAll _ ∅ _ "t" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@Predicate (Tree · ∅) Z
	(fun '(t, tt) => (prop_UnionUnionIdem t, 0%Z))).

Definition test_prop_UnionUnionIdem_runner := (targetLoop 20000 test_prop_UnionUnionIdem (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionIdem_runner. *)

Definition test_prop_UnionUnionAssoc   :=
	@ForAll _ ∅ _ "t1" (fun tt => bespoke) (fun tt n => (fun n => arbitrary)) (fun tt n => shrink n) (fun tt n => show n) (
	@ForAll _ (Tree · ∅) _ "t2" (fun '(t1, tt) => bespoke) (fun '(t1, tt) n => (fun n => arbitrary)) (fun '(t1, tt) n => shrink n) (fun '(t1, tt) n => show n) (
	@ForAll _ (Tree · (Tree · ∅)) _ "t3" (fun '(t2, (t1, tt)) => bespoke) (fun '(t2, (t1, tt)) n => (fun n => arbitrary)) (fun '(t2, (t1, tt)) n => shrink n) (fun '(t2, (t1, tt)) n => show n) (
	@Predicate (Tree · (Tree · (Tree · ∅))) Z
	(fun '(t3, (t2, (t1, tt))) => (prop_UnionUnionAssoc t1 t2 t3, 0%Z))))).

Definition test_prop_UnionUnionAssoc_runner := (targetLoop 20000 test_prop_UnionUnionAssoc (DynamicResettingSingletonPool.(mkPool) tt) DynamicResettingSingletonPool HillClimbingUtility).
(*! QuickProp test_prop_UnionUnionAssoc_runner. *)
