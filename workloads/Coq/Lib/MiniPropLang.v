From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Coq.Program.Wf.
Require Import Lia.
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

Inductive RunResult {C: Ctx} {F: Type} (cprop : CProp C F) :=
| Normal : ⟦⦗cprop⦘⟧ -> option bool -> F -> RunResult cprop
.
Arguments Normal {C} {F} {cprop}.

Fixpoint genAndRun {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (RunResult cprop).
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (bindGen (@genAndRun (A · C) F cprop' (a, env)) (fun res => _)).
    destruct res as [env' truth feedback].
    + refine (ret (Normal _ truth feedback)).
      simpl in *.
      refine (a, _).
      refine env'.
  - intros env.
    destruct (prop env).
    refine (ret (Normal _ o f)).
    simpl in *.
    refine tt.
Defined.
(*
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        bindGen (gen env) (fun a =>
        bindGen (@genAndRun _ _ cprop' (a,env)) (fun res =>
        match res with
        | Normal env' truth feedback => _
        | Discard env' feedback => _
        end))
  | ForAllMaybe _ _ _ _ gen mut shr pri cprop' =>
      fun env => _
  | Predicate C F prop =>
      fun env => ret (Some (tt, prop env))
  end
.*)
(*
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        res <- genAndRun cprop' (a,env);;
        match res with
        | Normal env' truth feedback =>
            ret (Normal (a,env') truth feedback)
        | Discard env' feedback =>
            ret (Discard (Some a, env') feedback)
        end
  | Predicate C F prop =>
      fun env => ret (Some (tt, prop env))
  end.*)

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
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)).
  Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(bindGen (@mutAll (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
    refine (ret (x', xs')).
  - intros env _.
    refine (ret tt).
Defined.  

Fixpoint mutSome {C : Ctx} {F : Type}
  (cprop : CProp C F) (t: nat)
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⦗cprop⦘⟧)).
Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? prop].

  - intros env (x,xs).
    simpl in *.
    refine(bindGen (choose(0,1)) (fun mut_oracle => _)).
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(bindGen (@mutSome (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
    refine(match mut_oracle with 0 => ret (x', xs') | _ => ret (x, xs') end).
  - intros env _.
    refine (ret tt).
Defined.


Fixpoint print {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env (a,inps').
    refine ((name, pri env a) :: (print (A · C) F cprop' (a, env) inps')).
  - intros env _.
    refine nil.
Defined. 

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

Module QueuePool.
  Local Open Scope list_scope.
  Definition t {A F: Type} := list (@Seed A F).

  Definition mkQueuePool {A F: Type} : unit -> @t A F :=
    fun _ => nil.

  Definition is_empty {A F: Type} (q: @t A F) : bool :=
    match q with
    | [] => true
    | _ => false
    end.

  Definition push_front {A F: Type} (seed: @Seed A F) (q: @t A F) : @t A F :=
    q ++ [seed].
  
  Definition push_back {A F: Type} (seed: @Seed A F) (q: @t A F) : @t A F :=
    seed :: q.

  Definition pop_back {A F: Type} (q: @t A F) : option (@Seed A F * @t A F) :=
    match q with
    | [] => None
    | h :: t => Some (h, t)
    end.

  Definition pop_front {A F: Type} (q: @t A F) : option (@Seed A F * @t A F) :=
    match rev q with
    | [] => None
    | h :: t => Some (h, rev t)
    end.

End QueuePool.

Import QueuePool.


#[global] Instance QueueSeedPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@QueuePool.t A F) :=
{| mkPool _ := QueuePool.mkQueuePool tt;
  invest seed pool := match seed with 
                      | (a, f) => QueuePool.push_front (mkSeed a f 1) pool
                      end ;
  revise pool a _ :=  match QueuePool.pop_front pool with
                      | None => pool
                      | Some (h, t) => 
                        let a' := input h in
                        if (a = a')? then 
                          let f := feedback h in
                          let n := energy h in
                          if (n =? 0) then t
                          else QueuePool.push_front (mkSeed a f (n - 1)) t
                        else pool
                      end ;
  sample pool := match QueuePool.pop_back pool with
                 | None => Generate
                 | Some(h, _) => if (energy h =? 0) 
                              then Generate
                              else Mutate h (energy h - 1)
                 end ;
  best pool := let fix maxSeed (cmax: option (@Seed A F)) (q: @t A F) `{Scalar F} : option (@Seed A F) :=
                match q with
                | [] => cmax
                | h :: t => match cmax with
                            | None => maxSeed (Some h) t
                            | Some seed => if ((scale (feedback h)) >? (scale (feedback seed))) then maxSeed (Some h) t else maxSeed (Some seed) t
                            end
                end in
                maxSeed None pool
|}.

Module LeftistHeap.

  Inductive LTree (A : Type) : Type :=
  | E : LTree A
  | N : nat -> A -> LTree A -> LTree A -> LTree A.

  Arguments E {A}.
  Arguments N {A} _ _ _ _.

  Definition right_spine {A : Type} (t : LTree A) : nat :=
  match t with
    | E => 0
    | N r _ _ _ => r
  end.

  Inductive LeftBiased {A : Type} : LTree A -> Prop :=
    | LeftBiased_E : LeftBiased E
    | LeftBiased_N :
        forall (v : A) (l r : LTree A),
          (right_spine r <= right_spine l)%nat ->
          LeftBiased l -> LeftBiased r ->
            LeftBiased (N (1 + right_spine r) v l r).

  Inductive Elem {A : Type} (x : A) : LTree A -> Prop :=
    | Elem_root :
        forall (n : nat) (l r : LTree A), Elem x (N n x l r)
    | Elem_l :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x l -> Elem x (N n v l r)
    | Elem_r :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x r -> Elem x (N n v l r).

  Definition Heap {A F: Type} := LTree (@Seed A F).

  Definition seed_in_z {A F: Type} `{Scalar F} (x: @Seed A F) : Z := scale (feedback x).

  Inductive isHeap {A F: Type} `{Scalar F} : @Heap A F -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall  (n: nat) (v: Seed) (l r : Heap),
          (forall x : @Seed A F, Elem x l -> seed_in_z v >= seed_in_z x) -> isHeap l ->
          (forall x : @Seed A F, Elem x r -> seed_in_z v >= seed_in_z x) -> isHeap r ->
            isHeap (N n v l r).

  #[global] Hint Constructors LTree LeftBiased Elem isHeap : core.

  Definition balance {A F: Type}
    (v : @Seed A F) (l r : Heap) : Heap :=
    if (right_spine r <=? right_spine l)%nat
    then N (1 + right_spine r) v l r
    else N (1 + right_spine l) v r l.

  Fixpoint size {A F: Type} (t : @Heap A F) : nat :=
  match t with
    | E => 0
    | N _ _ l r => 1 + size l + size r
  end.

  Definition sum_of_sizes
    {A F: Type}
    (p : @Heap A F * @Heap A F) : nat :=
    size (fst p) + size (snd p).

  Function merge {A F: Type} (p : @Heap A F * @Heap A F) (witness: Scalar F) {measure sum_of_sizes p} : @Heap A F :=
  match p with
    | (E, t2) => t2
    | (t1, E) => t1
    | (N _ v l r as t1, N _ v' l' r' as t2) =>
        if ((seed_in_z v) >=? (seed_in_z v'))%Z
        then balance v l (merge (r, t2) witness)
        else balance v' l' (merge (t1, r') witness)
  end.
  Proof.
  1-2: intros; cbn; lia.
  Defined.

  Definition empty {A F: Type} (tt: unit) : @Heap A F := E.

  Definition isEmpty {A F: Type} (t : @Heap A F) : bool :=
  match t with
    | E => true
    | _ => false
  end.

  Definition singleton {A F: Type} (x : @Seed A F) : Heap := N 1 x E E.

  Definition insert {A F: Type} `{w: Scalar F} (x : @Seed A F) (t : Heap) : Heap :=
  @merge A F (singleton x, t) w.

  Definition findMax {A F: Type} (t : Heap) : option (@Seed A F) :=
  match t with
    | E => None
    | N _ v _ _ => Some v
  end.

  Definition deleteMax {A F: Type} `{w: Scalar F} (t : Heap) : option Seed * Heap :=
  match t with
    | E => (None, E)
    | N _ v l r => (Some v, @merge A F (l, r) w)
  end.

  Definition extractMax {A F: Type} `{w: Scalar F}
  (t : Heap) : option (Seed * Heap) :=
  match t with
    | E => None
    | N _ v l r => Some (v, @merge A F (l, r) w)
  end.

End LeftistHeap.

#[global] Instance HeapSeedPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@LeftistHeap.Heap A F) :=
{| mkPool _ := LeftistHeap.empty tt;
  invest seed pool := match seed with 
                      | (a, f) => LeftistHeap.insert (mkSeed a f 100) pool
                      end ;
  revise pool a _ :=  match LeftistHeap.extractMax pool with
                      | None => pool
                      | Some (seed, rest) => 
                        let a' := input seed in
                        if (a = a')? then 
                          let f := feedback seed in
                          let n := energy seed in
                          if (n =? 0) then rest
                          else LeftistHeap.insert (mkSeed a f (n - 1)) rest
                        else pool
                      end ;
  sample pool := match LeftistHeap.extractMax pool with
                 | None => Generate
                 | Some (seed, _) => Mutate seed 0
                 end ;
  best pool := match LeftistHeap.extractMax pool with
               | None => None
               | Some (seed, _) => Some seed
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

Record Result := {
 discards: nat;
 foundbug: bool;
 passed: nat;
 counterexample: list (string * string);
}.

Definition mkResult 
  (discards: nat)
  (foundbug: bool)
  (passed: nat)
  (counterexample: list (string * string))
  : Result := {| discards := discards; foundbug := foundbug; passed := passed; counterexample := counterexample |}.

#[global] Instance showResult : Show Result :=
  {| show r := """discards"": " ++ show (discards r) ++
               ", ""foundbug"": " ++ show (foundbug r) ++
               ", ""passed"": " ++ show (passed r) ++
               ", ""counterexample"": """ ++  showElemList (counterexample r) ++ """"
  |}.

Definition runLoop (fuel : nat) (cprop : CProp ∅ Z): G Result :=  
  let fix runLoop'
    (fuel : nat) 
    (cprop : CProp ∅ Z) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
    seed <- justGen cprop tt;;
    let res := runAndTest cprop tt seed in
    let '(truth, feedback) := res in
      match truth with
      | Some false =>
        (* Fails *)
        let shrinkingResult := shrinkLoop 10 cprop seed in
        let printingResult := print cprop tt shrinkingResult in
        ret (mkResult discards true (passed + 1) printingResult)
      | Some true =>
        (* Passes *)
        runLoop' fuel' cprop (passed + 1)%nat discards
      | None => 
        (* Discard *)
        runLoop' fuel' cprop passed (discards + 1)%nat
      end
    end in
    runLoop' fuel cprop 0%nat 0%nat
    .


Definition targetLoop
  (fuel : nat) 
  (cprop : CProp ∅ Z)
  {Pool : Type}
  {poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool}
  (seeds : Pool)
  (utility: Utility) : G Result :=

  let fix targetLoop' 
         (fuel : nat) 
         (passed : nat)
         (discards: nat)
         (cprop : CProp ∅ Z)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility) : G Result :=
        match fuel with
        | O => ret (mkResult discards false passed [])
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
                ret (mkResult discards true (passed + 1) printingResult)
            | Some true =>
                (* Passes *)
                match useful seeds feedback with
                | true =>
                    let seeds' := invest (seed, feedback) seeds in
                    targetLoop' fuel' (passed + 1)%nat discards cprop seeds' poolType utility
                | false =>
                    let seeds' := match directive with
                                  | Generate => seeds
                                  | Mutate source _ => revise seeds (input source) (seed, feedback)
                                  end in
                    targetLoop' fuel' (passed + 1)%nat discards cprop seeds' poolType utility
                end
            | None => 
                (* Discard *)
                targetLoop' fuel' passed (discards + 1)%nat cprop seeds poolType utility
            end
        end in
        targetLoop' fuel 0%nat 0%nat cprop seeds poolType utility.

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


Definition example4 :=
  @ForAll _ ∅ _ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
            (fun '(y, (x, tt)) => 
              let '(res, feedback) := withInstrumentation (fun _ => test2 x y) in
              (res, Z.of_nat(snd feedback)))
            )).
            

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

(* Definition bench_prl_function := (targetLoop 100000 bench_prl (mkPool tt) StaticSingletonPool HillClimbingUtility).
Definition bench_transformed := toMonad bench_prl tt.
Definition qctest_bench_qc := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (quickCheckWith (updMaxSuccess (updAnalysis stdArgs true) 100000) bench_qc))) ++ "}|]")).
Definition qctest_bench_prl := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 bench_prl_function))) ++ "}|]")). *)


(* Definition qctest_bench_transformed := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (quickCheckWith (updMaxSuccess (updAnalysis stdArgs true) 100000) bench_transformed))) ++ "}|]")).

Extraction "bench.ml" qctest_bench_qc qctest_bench_prl qctest_bench_transformed. *)

(* Sample1 (targetLoopLogged 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility nil). *)
(* Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility nil). *)
(* Sample1 (targetLoopLogged 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility nil). *)
Definition test_prop_UnionUnionAssoc_runner := (targetLoopLogged 1000 example4 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility nil).
Definition qctest_test_prop_InsertValid := (fun _ : unit => print_extracted_coq_string ("[|{" ++ show (withTime(fun tt => (sample1 test_prop_UnionUnionAssoc_runner))) ++ "}|]")).

Extraction "bench.ml" qctest_test_prop_InsertValid.



(* Sample1 (targetLoop 1000 example3 (StaticSingletonPool.(mkPool) tt)  HillClimbingUtility). *)
(* Sample1 (runLoop 1000 example3). *)
(* Sample1 (targetLoopLogged 1000 example5 (mkPool tt) StaticSingletonPool HillClimbingUtility nil). *)


(* Sample1 (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility). *)
(* Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility). *)
(* Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility). *)
