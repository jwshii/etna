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
| ForAllMaybe : forall A C F
      (name: string)
      (generator : ⟦C⟧ -> G (option A))
      (mutator   : ⟦C⟧ -> nat -> A -> G (option A))
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
  | ForAllMaybe A C _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | Predicate _ _ _ => ∅
  end.

Fixpoint inputTypesMaybe {C : Ctx} {F : Type}
         (cprop : CProp C F) : Ctx :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' =>
      (option A) · (inputTypesMaybe cprop')
  | ForAllMaybe A C _ _ _ _ _ _ cprop' =>
      (option A) · (inputTypesMaybe cprop')
  | Predicate _ _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@inputTypes _ _ c).
Notation "'⟬' c '⟭'" := (@inputTypesMaybe _ _ c).

Fixpoint noneTypes {C : Ctx} {F : Type}
         (cprop : CProp C F) : ⟦⟬cprop⟭⟧ :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' =>
      (None, noneTypes cprop')
  | ForAllMaybe A C _ _ _ _ _ _ cprop' =>
      (None, noneTypes cprop')
  | Predicate _ _ _ => tt
  end.

Definition typeHead {C : Ctx} {F : Type}
         (cprop : CProp C F) : Type :=
  match cprop with
  | ForAll A C _ _ _ _ _ _ cprop' => A
  | ForAllMaybe A C _ _ _ _ _ _ cprop' => A
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
| Discard : ⟦⟬cprop⟭⟧ -> RunResult cprop
.
Arguments Normal {C} {F} {cprop}.
Arguments Discard {C} {F} {cprop}.

Fixpoint genAndRun {C : Ctx} {F : Type}
         (cprop : CProp C F)
  : ⟦C⟧ -> G (RunResult cprop).
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (bindGen (@genAndRun (A · C) F cprop' (a, env)) (fun res => _)).
    destruct res as [env' truth feedback | env' feedback].
    + refine (ret (Normal _ truth feedback)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _)).
      simpl in *.
      refine (Some a, env').
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@genAndRun (A · C) F cprop' (a, env)) (fun res => _)).
      destruct res as [env' truth feedback | env' feedback].
      + refine (ret (Normal _ truth feedback)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _)).
      simpl in *.
      refine (None, _).
      refine (noneTypes cprop').
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
  : ⟦C⟧ -> G (⟦⟬cprop⟭⟧) :=
  match cprop with
  | ForAll _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        env <- justGen cprop' (a,env);;
        ret (Some a,env)
  | ForAllMaybe _ _ _ _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        match a with
        | Some a => env <- justGen cprop' (a,env);;
                    ret (Some a,env)
        | None => ret (None, noneTypes cprop')
        end
  
  | Predicate C F prop =>
      fun env => ret tt
  end.

Fixpoint mutAll {C : Ctx} {F : Type}
         (cprop : CProp C F) (t: nat)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
  Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(bindGen (@mutAll (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
    refine (ret (Some x', xs')).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mutAll (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, noneTypes _)).
  - intros env _.
    refine (ret tt).
Defined.  

Fixpoint mutSome {C : Ctx} {F : Type}
  (cprop : CProp C F) (t: nat)
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? ? ? gen mut shr pri cprop'
                    |? ? prop].

  - intros env (x,xs).
    simpl in *.
    refine(bindGen (choose(0,1)) (fun mut_oracle => _)).
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(bindGen (@mutSome (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
    refine(match mut_oracle with 0 => ret (Some x', xs') | _ => ret (Some x, xs') end).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env t x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mutSome (A · C) F cprop' t (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, noneTypes _)).
  - intros env _.
    refine (ret tt).
Defined.


Fixpoint print {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env (a,inps').
    refine ((name, pri env a) :: (print (A · C) F cprop' (a, env) inps')).
  - intros env (a,inps').
    refine ((name, pri env a) :: (print (A · C) F cprop' (a, env) inps')).
  - intros env _.
    refine nil.
Defined. 

Definition pri_opt {A} (pri: A -> string) (a: option A) : string :=
  match a with
  | Some a => "Some (" ++ pri a ++ ")"
  | None => "None"
  end.

Fixpoint ctx_opt (C: Ctx) : Type :=
  match C with
  | ∅ => unit
  | T·C => option T * ctx_opt C
  end.

Fixpoint print_opt {C : Ctx} {F} (cprop : CProp C F)
  : ⟦C⟧ -> ⟦⟬ cprop ⟭⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? ? gen mut shr pri cprop'
                    |? ? ? ? gen mut shr pri cprop'
                    |? ? prop].
  - intros env (a,inps'). 
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) F cprop' (a, env) inps'
            | None => nil
            end).
  - intros env (a,inps').
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) F cprop' (a, env) inps'
            | None => nil
            end).
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


Definition pullValues {C: Ctx} {F: Type} (cprop: CProp C F) (opt_values: ⟦⟬cprop⟭⟧) : option ⟦⦗cprop⦘⟧.
Proof.
  induction cprop; simpl in *.
  - destruct opt_values as [a opt_values'].
    apply IHcprop in opt_values'.
    refine(
      match a, opt_values' with
      | Some a, Some values' => Some (a, values')
      | _, _ => None
      end).
  - destruct opt_values as [a opt_values'].
    apply IHcprop in opt_values'.
    refine(
      match a, opt_values' with
      | Some a, Some values' => Some (a, values')
      | _, _ => None
      end).
  - exact (Some tt).
Defined.

Fixpoint runLoop (fuel : nat) (cprop : CProp ∅ Z): G (list (string * string)) :=
  match fuel with
  | O => ret []
  | S fuel' => 
  opt_seed <- justGen cprop tt;;
  match pullValues cprop opt_seed with
    | None => runLoop fuel' cprop
    | Some seed =>
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
      end
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

Instance showResult : Show Result :=
  {| show r := """discards"": " ++ show (discards r) ++
               ", ""foundbug"": " ++ show (foundbug r) ++
               ", ""passed"": " ++ show (passed r) ++
               ", ""counterexample"": """ ++  showElemList (counterexample r) ++ """"
  |}.

Definition targetLoop
  (fuel : nat) 
  (cprop : CProp ∅ Z)
  {Pool : Type}
  (seeds : Pool)
  (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
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
            opt_seed <- generator cprop directive;;
            match pullValues cprop opt_seed with
            | None => targetLoop' fuel' passed (discards + 1)%nat cprop seeds poolType utility
            | Some seed =>
              let res := runAndTest cprop tt seed in
              let '(truth, feedback) := res in
              match truth with
              | Some false =>
                  (* Fails *)
                  let shrinkingResult := shrinkLoop 10 cprop seed in
                  let printingResult := print cprop tt shrinkingResult in
                  ret (mkResult discards true passed printingResult)
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
  | ForAllMaybe A C F name gen mut shr pri cprop' =>
    fun env =>
      forAllShrinkShowMaybe (gen env) (shr env) (pri env) (fun a => toMonad cprop' (a, env))
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
      opt_seed <- generator cprop directive;;
      match pullValues cprop opt_seed with
      | None => 
      let printedSeed := showElemList (print_opt cprop tt opt_seed) in
      let printedSource := match directive with 
                          | Generate => "None"
                          | Mutate seed _ => printSeed cprop seed
                          end in
      let log := ("source: [" ++ printedSource ++ "], seed: [" ++ printedSeed ++ ", fuel: " ++ show fuel ++ ", directive:" ++ show directive) :: log in
        targetLoopLogged fuel' cprop seeds poolType utility log
      | Some seed =>
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




Definition arb_opt : G (option nat) :=
  choose (0, 1) >>= fun n => match n with
                            | 0 => ret None
                            | _ => choose (0, 1000)%nat >>= fun n => ret (Some n)
                            end.

Definition mut_opt (n: option nat) (t: nat) : G (option nat) :=
  match n with
  | Some n => choose (0, 1) >>= fun m => match m with
                                        | 0 => ret (Some (n - t)%nat)
                                        | _ => ret (Some (n + t)%nat)
                                        end
  | None => ret None
  end.

Definition example5 :=
  @ForAllMaybe _ ∅ _ "x" (fun tt => arb_opt) (fun tt n => mut_opt None) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) _ "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Predicate (nat · (nat · ∅)) Z
              (fun '(y, (x, tt)) => (test2 x y, (2000 - Z.of_nat(x - y) - Z.of_nat(y - x)))))).
    
(* Sample1 (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility). *)
(* Sample1 (targetLoopLogged 1000 example5 (mkPool tt) StaticSingletonPool HillClimbingUtility nil). *)


(* Sample1 (targetLoop 1000 example3 (mkPool tt) StaticSingletonPool HillClimbingUtility). *)
(* Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicMonotonicSingletonPool HillClimbingUtility). *)
(* Sample1 (targetLoop 1000 example3 (mkPool tt) DynamicResettingSingletonPool HillClimbingUtility). *)
