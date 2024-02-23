From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import Coq.Program.Wf.
Require Import Lia.
Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

Axiom withInstrumentation : (unit -> bool) -> (bool * (bool * nat)).
Extract Constant withInstrumentation => "withInstrumentation".

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

Inductive CProp : Ctx -> Type :=
| ForAll : forall
      {A: Type}
      {C: Ctx}
      (name: string)
      (generator : ⟦C⟧ -> G A)
      (mutator   : ⟦C⟧ -> A -> G A)
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) -> CProp C
| ForAllMaybe : forall
      {A: Type}
      {C: Ctx}
      (name: string)
      (generator : ⟦C⟧ -> G (option A))
      (mutator   : ⟦C⟧ -> A -> G (option A))
      (shrinker  : ⟦C⟧ -> A -> list A)
      (printer   : ⟦C⟧ -> A -> string),
      CProp (A · C) -> CProp C
| Implies : forall C
      (prop : ⟦C⟧ -> bool),
      CProp C -> CProp C 
| Check : forall C,
      (⟦C⟧ -> bool) -> CProp C.

Fixpoint inputTypes {C : Ctx}
         (cprop : CProp C) : Ctx :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      A · (inputTypes cprop')
  | Implies _ _ cprop' => (inputTypes cprop')
  | Check _ _ => ∅
  end.

Fixpoint inputTypesMaybe {C : Ctx}
         (cprop : CProp C) : Ctx :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      (option A) · (inputTypesMaybe cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      (option A) · (inputTypesMaybe cprop')
  | Implies _ _ cprop' => (inputTypesMaybe cprop')
  | Check _ _ => ∅
  end.

Notation "'⦗' c '⦘'" := (@inputTypes _ c).
Notation "'⟬' c '⟭'" := (@inputTypesMaybe _ c).

Fixpoint noneTypes {C : Ctx}
         (cprop : CProp C) : ⟦⟬cprop⟭⟧ :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' =>
      (None, noneTypes cprop')
  | @ForAllMaybe A _ _ _ _ _ _ cprop' =>
      (None, noneTypes cprop')
  | Implies _ _ cprop' => noneTypes cprop'
  | Check _ _ => tt
  end.

Definition typeHead {C : Ctx}
         (cprop : CProp C) : Type :=
  match cprop with
  | @ForAll A _ _ _ _ _ _ cprop' => A
  | @ForAllMaybe A _ _ _ _ _ _ cprop' => A
  | Implies _ _ cprop' => unit
  | Check _ _ => unit
  end.


Definition arb : G nat := choose (0,10).
Definition gen (n : nat) : G nat := choose (0, n).
Definition mut (n : nat) : G nat :=
  choose (n - 3, n + 3).
Definition test (x y : nat) : bool := Nat.ltb y x.

Local Open Scope string.

Definition example :=
  @Implies (nat · (nat · ∅)) (fun '(y, (x, tt)) => Nat.ltb x y) (
  @Check (nat · (nat · ∅)) (fun '(y, (x, tt)) => test x y)).

Definition example' :=
  ForAll "x" (fun tt => arb) (fun tt => mut) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
             (fun '(y, (x, tt)) => test x y))).

Inductive DiscardType := PreconditionFailure | GenerationFailure.

Inductive RunResult {C: Ctx} (cprop : CProp C) :=
| Normal : ⟦⦗cprop⦘⟧ -> bool -> RunResult cprop
| Discard : ⟦⟬cprop⟭⟧ -> DiscardType -> RunResult cprop.

Arguments Normal {C} {cprop}.
Arguments Discard {C} {cprop}.

Fixpoint genAndRun {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> G (RunResult cprop).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (bindGen (@genAndRun (A · C) cprop' (a, env)) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine (Some a, env').
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@genAndRun (A · C) cprop' (a, env)) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure)).
      simpl in *.
      refine (None, _).
      refine (noneTypes cprop').
  - intros env.
    destruct (prop env).
    * refine (bindGen (@genAndRun C cprop' env) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine env'.
    * refine (ret (Discard _ PreconditionFailure)).
      + simpl in *.
        refine (noneTypes cprop').
  - intros env.
    refine (ret (Normal _ (prop env))).
    refine tt.
Defined.


Fixpoint justGen {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> G (⟦⟬cprop⟭⟧) :=
  match cprop with
  | ForAll _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        env <- justGen cprop' (a,env);;
        ret (Some a,env)
  | ForAllMaybe  _ gen mut shr pri cprop' =>
      fun env =>
        a <- gen env;;
        match a with
        | Some a => env <- justGen cprop' (a,env);;
                    ret (Some a,env)
        | None => ret (None, noneTypes cprop')
        end
  | Implies _ _ cprop' =>
      fun env => justGen cprop' env
  | Check C prop =>
      fun env => ret tt
  end.

Fixpoint mutAll {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
  Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(bindGen (@mutAll (A · C) cprop' (x', env) xs) (fun xs' => _)).
    refine (ret (Some x', xs')).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mutAll (A · C) cprop' (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, noneTypes _)).
  - intros env xs.
    simpl in *.
    refine(bindGen (@mutAll C cprop' env xs) (fun xs' => _)).
    refine (ret xs').
  - intros env _.
    refine (ret tt).
Defined.  

Fixpoint mutSome {C : Ctx}
  (cprop : CProp C) 
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> (G (⟦⟬cprop⟭⟧)).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (choose(0,1)) (fun mut_oracle => _)).
    refine(bindGen (mut env x) (fun x' => _)).
    refine(bindGen (@mutSome (A · C) cprop' (x', env) xs) (fun xs' => _)).
    refine(match mut_oracle with 0 => ret (Some x', xs') | _ => ret (Some x, xs') end).
  - intros env (x,xs).
    simpl in *.
    refine(bindGen (mut env x) (fun x' => _)).
    refine(match x' with Some x' => _ | None => _ end).
    * refine(bindGen (@mutSome (A · C) cprop' (x', env) xs) (fun xs' => _)).
      refine (ret (Some x', xs')).
    * refine (ret (None, noneTypes _)).
  - intros env xs.
    simpl in *.
    refine(bindGen (@mutSome C cprop' env xs) (fun xs' => _)).
    refine (ret xs').
  - intros env _.
    refine (ret tt).
Defined.


Fixpoint print {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗ cprop ⦘⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (a,inps').
    refine ((name, pri env a) :: (print (A · C) cprop' (a, env) inps')).
  - intros env (a,inps').
    refine ((name, pri env a) :: (print (A · C) cprop' (a, env) inps')).
  - intros env inps'.
    refine (print C cprop' env inps').
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

Fixpoint print_opt {C : Ctx} (cprop : CProp C)
  : ⟦C⟧ -> ⟦⟬ cprop ⟭⟧ -> list (string * string).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (a,inps'). 
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) cprop' (a, env) inps'
            | None => nil
            end).
  - intros env (a,inps').
    refine ((name, pri_opt (pri env) a) :: _).
    refine (match a with
            | Some a => print_opt (A · C) cprop' (a, env) inps'
            | None => nil
            end).
  - intros env inps'.
    refine (print_opt C cprop' env inps').
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
| Mutate : @Seed A F -> Directive
.

#[global] Instance showDirective {A F: Type} `{Show (@Seed A F)}  : Show (@Directive A F) :=
{|
  show d := match d with
            | Generate => "Generate"
            | Mutate seed => "Mutate(" ++ show seed ++ ")"
            end
|}.


Class SeedPool {A F Pool: Type} := {
  (* Creates an empty pool. *)
  mkPool  : unit -> Pool;
  (* Adds a useful seed into the pool. *)
  invest  : (A * F) -> Pool -> Pool;
  (* Decreases the energy of a seed after a useless trial. *)
  revise  : Pool -> Pool;
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

  #[global] Instance ScalarNat : Scalar nat :=
  {| scale := fun x => Z.of_nat x |}.


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
     revise pool := pool ;
     sample pool := match seed pool with
                    | None => Generate
                    | Some seed => Mutate seed
                    end ;
     best pool := seed pool
  |}.

#[global] Instance DynamicMonotonicSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 20) |}
                        end ;
    revise pool :=  match seed pool with
                    | None => pool
                    | Some seed => 
                      let '{| input := a; feedback := f; energy := n |} := seed in
                      {| seed := Some (mkSeed a f (n - 1)) |}
                    end ;               
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else Mutate seed

                   end ;
    best pool := seed pool
|}.

#[global] Instance DynamicResettingSingletonPool {A F: Type} `{Dec_Eq A} `{Scalar F} : @SeedPool A F (@SingletonPool A F) :=
  {| mkPool _ := {| seed := None |};
    invest seed pool := match seed with 
                        | (a, f) => {| seed := Some (mkSeed a f 100) |}
                        end ;
    revise pool := match seed pool with
                   | None => pool
                   | Some seed => 
                     let '{| input := a; feedback := f; energy := n |} := seed in
                     {| seed := Some (mkSeed a f (n - 1)) |}
                   end ;
    sample pool := match seed pool with
                   | None => Generate
                   | Some seed => if (energy seed =? 0) 
                                    then Generate
                                    else Mutate seed
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
  revise pool :=  match QueuePool.pop_front pool with
                  | None => pool
                  | Some (h, t) => 
                      let '{| input := a; feedback := f; energy := n|} := h in
                      if (n =? 0) then t
                      else QueuePool.push_front (mkSeed a f (n - 1)) t
                  end ;
  sample pool := match QueuePool.pop_back pool with
                 | None => Generate
                 | Some(h, _) => if (energy h =? 0) 
                              then Generate
                              else Mutate h
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
  revise pool :=  match LeftistHeap.extractMax pool with
                  | None => pool
                  | Some (seed, rest) => 
                    let '{| input := a; feedback := f; energy := n|} := seed in
                    if (n =? 0) then rest
                    else LeftistHeap.insert (mkSeed a f (n - 1)) rest
                  end ;
  sample pool := match LeftistHeap.extractMax pool with
                 | None => Generate
                 | Some (seed, _) => Mutate seed
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



Fixpoint runAndTest {C:Ctx} (cprop : CProp C)
         (cenv : ⟦C⟧)
         (fenv :  ⟦⦗cprop⦘⟧)
         {struct cprop}
  : option bool.
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
  - destruct (prop cenv) eqn:E.
    + apply IHcprop.
      * exact cenv.
      * exact fenv.
    + exact None.
  - exact (Some (b cenv)).
Defined.

Fixpoint instrumentedRunAndTest {C:Ctx} (cprop : CProp C)
         (cenv : ⟦C⟧)
         (fenv :  ⟦⦗cprop⦘⟧)
         {struct cprop}
  : option bool * Z.
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
  - refine (
    let '(res, (useful, energy)) := withInstrumentation (fun _ => (prop cenv)) in
    if res then _
    else (None, Z.of_nat energy)
    ).
    apply IHcprop.
    + exact cenv.
    + exact fenv.
  - refine (
      let '(res, (useful, energy)) := withInstrumentation (fun _ => (b cenv)) in
      (Some res, Z.of_nat energy)
    ).
Defined.



Fixpoint shrinkOnTheFly
  {C : Ctx}
  (cprop : CProp C)
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
    + destruct (shrinkOnTheFly _ cprop (a,cenv) fenv') eqn:M.
      * exact (Some (a, i)).
      * exact None.
    (* More shrinks - run the property on the shrunk possibility. *)
    + destruct (runAndTest cprop (a0,cenv) fenv') eqn:T.
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
  + destruct (shrinkOnTheFly _ cprop (a,cenv) fenv') eqn:M.
    * exact (Some (a, i)).
    * exact None.
  (* More shrinks - run the property on the shrunk possibility. *)
  + destruct (runAndTest cprop (a0,cenv) fenv') eqn:T.
    * destruct b.
      (* Test succeeded - recurse down the list. *)
      -- apply IHl.
      (* Test failed - end with current result. *)
      -- exact (Some (a0, fenv')).     
    * (* Test discarded - recurse down the list. *)
      apply IHl.
  -  destruct (runAndTest cprop cenv fenv) eqn:T.
    * destruct b.
      -- apply IHcprop.
        ++ exact cenv.
        ++ exact fenv.
      -- exact None.
    * exact None.
  - exact None.
Defined.

Fixpoint shrinkLoop(fuel : nat)
  (cprop: CProp ∅) (counterexample : ⟦⦗cprop⦘⟧) :
  ⟦⦗cprop⦘⟧ :=
  match fuel with
  | O => counterexample
  | S fuel' =>
      match shrinkOnTheFly cprop tt counterexample with
      | Some c' => shrinkLoop fuel' cprop c'
      | None => counterexample
      end
  end.

Definition generator (cprop: CProp ∅) (directive: @Directive ⟦⦗cprop⦘⟧ Z) :=
  match directive with
  | Generate => justGen cprop tt
  | Mutate seed => mutAll cprop tt (input seed)
  end.


Definition pullValues {C: Ctx} (cprop: CProp C) (opt_values: ⟦⟬cprop⟭⟧) : option ⟦⦗cprop⦘⟧.
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
  - apply IHcprop in opt_values.
    refine(
      match opt_values with
      | Some values => Some values
      | _ => None
      end). 
  - exact (Some tt).
Defined.



Fixpoint mutAndRun {C : Ctx}
         (cprop : CProp C)
  : ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> G (RunResult cprop).
Proof.
  destruct cprop as [? ? ? gen mut shr pri cprop'
                    |? ? ? gen mut shr pri cprop'
                    |? prop cprop'
                    |? prop].
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (bindGen (@mutAndRun (A · C) cprop' (a, env) xs) (fun res => _)).
    destruct res as [env' truth | env' discard_type].
    + refine (ret (Normal _ truth)).
      simpl in *.
      refine (a, _).
      refine env'.
    + refine (ret (Discard _ discard_type)).
      simpl in *.
      refine (Some a, env').
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@mutAndRun (A · C) cprop' (a, env) xs) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine (a, _).
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure)).
      simpl in *.
      refine (None, _).
      refine (noneTypes cprop').
  - intros env seed.
    destruct (prop env).
    * refine (bindGen (@mutAndRun C cprop' env seed) (fun res => _)).
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth)).
        simpl in *.
        refine env'.
      + refine (ret (Discard _ discard_type)).
        simpl in *.
        refine env'.
    * refine (ret (Discard _ PreconditionFailure)).
      + simpl in *.
        refine (noneTypes cprop').
  - intros env seed.
    refine (ret (Normal _ (prop env))).
    refine tt.
Defined.


Definition genAndRunWithDirective {C : Ctx} {F: Type}
         (cprop : CProp C) (d: @Directive ⟦⦗cprop⦘⟧ F)
  : ⟦C⟧ -> G (RunResult cprop) :=
  match d with
  | Generate => fun env => genAndRun cprop env
  | Mutate seed => fun env => mutAndRun cprop env (input seed)
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


Definition runLoop (fuel : nat) (cprop : CProp ∅): G Result :=  
  let fix runLoop'
    (fuel : nat) 
    (cprop : CProp ∅) 
    (passed : nat)
    (discards: nat)
    : G Result :=
    match fuel with
    | O => ret (mkResult discards false passed [])
    | S fuel' => 
        res <- genAndRun cprop tt;;
        match res with
        | Normal seed false =>
            (* Fails *)
            let shrinkingResult := shrinkLoop 10 cprop seed in
            let printingResult := print cprop tt shrinkingResult in
            ret (mkResult discards true (passed + 1) printingResult)
        | Normal _ true =>
            (* Passes *)
            runLoop' fuel' cprop (passed + 1)%nat discards
        | Discard _ _ => 
          (* Discard *)
          runLoop' fuel' cprop passed (discards + 1)%nat
        end
    end in
    runLoop' fuel cprop 0%nat 0%nat
    .



Axiom assert_false: forall {A: Type}, (unit -> A).
Extract Constant assert_false => "(fun _ -> assert false)

open Domainslib".


Axiom num_domains : nat.
Extract Constant num_domains => "Domain.recommended_domain_count () - 1".

Axiom TaskPool: Type.
Extract Constant TaskPool => "Domainslib.Task.pool".

Axiom pool : TaskPool.
Extract Constant pool => "Task.setup_pool ~num_domains ~name:""pool"" ()".

Axiom task_parallel_find : forall {A: Type}, TaskPool -> nat -> nat -> nat -> (nat -> option A) -> option A.
Extract Constant task_parallel_find => "
  (fun pool chunk_size start finish body ->
    Task.parallel_find pool ~chunk_size:chunk_size ~start:start ~finish:finish ~body:body)
".

Axiom task_run : forall {A: Type}, TaskPool -> (unit -> A) -> A.
Extract Constant task_run => "Task.run".

Axiom task_teardown_pool : TaskPool -> unit.
Extract Constant task_teardown_pool => "Task.teardown_pool".

Definition parLoop (fuel: nat) (cprop: CProp ∅) : G Result :=
  let parLoop' := (fun pool => 
    task_parallel_find pool 1%nat 0%nat num_domains (fun _ => 
      Some (runLoop fuel cprop)
    )
  ) in
  let res := task_run pool (fun _ => 
    match parLoop' pool with
    | None => assert_false tt
    | Some res => res
    end
  ) in
  let _ := task_teardown_pool pool in
  res.

Definition targetLoop
  (fuel : nat) 
  (cprop : CProp ∅)
  (feedback_function: ⟦⦗cprop⦘⟧ -> Z)
  {Pool : Type}
  {poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool}
  (seeds : Pool)
  (utility: Utility) : G Result :=
  let fix targetLoop' 
         (fuel : nat) 
         (passed : nat)
         (discards: nat)
         {Pool : Type}
         (seeds : Pool)
         (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
         (utility: Utility) : G Result :=
        match fuel with
        | O => ret (mkResult discards false passed [])
        | S fuel' => 
            let directive := sample seeds in
            res <- genAndRunWithDirective cprop directive tt;;
            match res with
            | Normal seed false =>
                (* Fails *)
                let shrinkingResult := shrinkLoop 10 cprop seed in
                let printingResult := print cprop tt shrinkingResult in
                ret (mkResult discards true (passed + 1) printingResult)
            | Normal seed true =>
                (* Passes *)
                let feedback := feedback_function seed in
                match useful seeds feedback with
                | true =>
                    let seeds' := invest (seed, feedback) seeds in
                    targetLoop' fuel' (passed + 1)%nat discards seeds' poolType utility
                | false =>
                    let seeds' := match directive with
                                  | Generate => seeds
                                  | Mutate source => revise seeds
                                  end in
                    targetLoop' fuel' (passed + 1)%nat discards seeds' poolType utility
                end
            | Discard _ _ => 
                (* Discard *)
                targetLoop' fuel' passed (discards + 1)%nat seeds poolType utility
            end
        end in
        targetLoop' fuel 0%nat 0%nat seeds poolType utility.


Fixpoint instrumentedMutAndRun {C : Ctx}
(cprop : CProp C)
: ⟦C⟧ -> ⟦⦗cprop⦘⟧ -> G (RunResult cprop * Z).
Proof.
destruct cprop as [? ? ? gen mut shr pri cprop'
           |? ? ? gen mut shr pri cprop'
           |? prop cprop'
           |? prop].
- intros env (x, xs).
  refine (bindGen (mut env x) (fun a => _)).
  refine (bindGen (@instrumentedMutAndRun (A · C) cprop' (a, env) xs) (fun res => _)).
  destruct res as [res feedback].
  destruct res as [env' truth | env' discard_type].
  + refine (ret (Normal _ truth, feedback)).
    simpl in *.
    refine (a, env').
  + refine (ret (Discard _ discard_type, feedback)).
    simpl in *.
    refine (Some a, env').
  - intros env (x, xs).
    refine (bindGen (mut env x) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@instrumentedMutAndRun (A · C) cprop' (a, env) xs) (fun res => _)).
      destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine (a, env').
      + refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure, 0)).
      simpl in *.
      refine (None, noneTypes cprop').
  - intros env seed.
    simpl in *.
    refine (
      let '(res, (useful, energy)) := withInstrumentation (fun _ => (prop env)) in
      if res then (bindGen (@instrumentedMutAndRun C cprop' env seed) (fun res => _))
      else (ret (Discard _ PreconditionFailure, (Z.of_nat energy)))
      ).
    + destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      * refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine env'.
      * refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine env'.
    + simpl in *.
      refine (noneTypes cprop').
    - intros env seed.
      refine (
        let '(res, (useful, energy)) := withInstrumentation (fun _ => (prop env)) in
        ret (Normal _ (prop env), (Z.of_nat energy))
        ).
      refine tt.
Defined.



Fixpoint instrumentedGenAndRun {C : Ctx}
(cprop : CProp C)
: ⟦C⟧ -> G (RunResult cprop * Z).
Proof.
destruct cprop as [? ? ? gen mut shr pri cprop'
           |? ? ? gen mut shr pri cprop'
           |? prop cprop'
           |? prop].
- intros env.
  refine (bindGen (gen env) (fun a => _)).
  refine (bindGen (@instrumentedGenAndRun (A · C) cprop' (a, env)) (fun res => _)).
  destruct res as [res feedback].
  destruct res as [env' truth | env' discard_type].
  + refine (ret (Normal _ truth, feedback)).
    simpl in *.
    refine (a, env').
  + refine (ret (Discard _ discard_type, feedback)).
    simpl in *.
    refine (Some a, env').
  - intros env.
    refine (bindGen (gen env) (fun a => _)).
    refine (match a with Some a => _ | None => _ end).
    * refine (bindGen (@instrumentedGenAndRun (A · C) cprop' (a, env)) (fun res => _)).
      destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      + refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine (a, env').
      + refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine (Some a, env').
    * refine (ret (Discard _ GenerationFailure, 0)).
      simpl in *.
      refine (None, noneTypes cprop').
  - intros env.
    simpl in *.
    refine (
      let '(res, (useful, energy)) := withInstrumentation (fun _ => (prop env)) in
      if res then (bindGen (@instrumentedGenAndRun C cprop' env) (fun res => _))
      else (ret (Discard _ PreconditionFailure, (Z.of_nat energy)))
      ).
    + destruct res as [res feedback].
      destruct res as [env' truth | env' discard_type].
      * refine (ret (Normal _ truth, feedback)).
        simpl in *.
        refine env'.
      * refine (ret (Discard _ discard_type, feedback)).
        simpl in *.
        refine env'.
    + simpl in *.
      refine (noneTypes cprop').
    - intros env.
      refine (
        let '(res, (useful, energy)) := withInstrumentation (fun _ => (prop env)) in
        ret (Normal _ (prop env), (Z.of_nat energy))
        ).
      refine tt.
Defined.

Definition instrumentedGenAndRunWithDirective {C : Ctx} {F: Type}
         (cprop : CProp C) (d: @Directive ⟦⦗cprop⦘⟧ F)
  : ⟦C⟧ -> G (RunResult cprop * Z) :=
  match d with
  | Generate => fun env => instrumentedGenAndRun cprop env
  | Mutate seed => fun env => instrumentedMutAndRun cprop env (input seed)
  end.


Definition fuzzLoop
(fuel : nat) 
(cprop : CProp ∅)
{Pool : Type}
{poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool}
(seeds : Pool)
(utility: Utility) : G Result :=
let fix fuzzLoop' 
        (fuel : nat) 
        (passed : nat)
        (discards: nat)
        {Pool : Type}
        (seeds : Pool)
        (poolType: @SeedPool (⟦⦗cprop⦘⟧) Z Pool)
        (utility: Utility) : G Result :=
      match fuel with
      | O => ret (mkResult discards false passed [])
      | S fuel' => 
          let directive := sample seeds in
          res <- instrumentedGenAndRunWithDirective cprop directive tt;;
          let '(res, feedback) := res in
          match res with
          | Normal seed false =>
              (* Fails *)
              let shrinkingResult := shrinkLoop 10 cprop seed in
              let printingResult := print cprop tt shrinkingResult in
              ret (mkResult discards true (passed + 1) printingResult)
          | Normal seed true =>
              (* Passes *)
              match useful seeds feedback with
              | true =>
                  let seeds' := invest (seed, feedback) seeds in
                  fuzzLoop' fuel' (passed + 1)%nat discards seeds' poolType utility
              | false =>
                  let seeds' := match directive with
                                | Generate => seeds
                                | Mutate _ => revise seeds
                                end in
                  fuzzLoop' fuel' (passed + 1)%nat discards seeds' poolType utility
              end
          | Discard _ _ => 
              (* Discard *)
              match directive with
              | Generate => fuzzLoop' fuel' passed (discards + 1)%nat seeds poolType utility
              | Mutate source =>
                let feedback := Z.div feedback 3 in
                match useful seeds feedback with
                | true =>
                    fuzzLoop' fuel' passed (discards+1)%nat seeds poolType utility
                | false =>
                    fuzzLoop' fuel' passed (discards+1)%nat (revise seeds) poolType utility
                end
              end
          end
      end in
      fuzzLoop' fuel 0%nat 0%nat seeds poolType utility.

Definition test2 (x y : nat) : bool :=
  (negb (Nat.eqb y  x)).


Definition example2 :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, tt)) => test2 x y))).

Definition example3 :=
  @ForAll _ ∅ "x" (fun tt => arb) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @ForAll _ (nat · ∅) "y" (fun '(x, tt) => gen x) (fun tt n => mut n) (fun tt n => shrink n) (fun tt n => show n) (
  @Check (nat · (nat · ∅))
              (fun '(y, (x, tt)) => (test2 x y)))).

  Definition fb :=
  (fun '(y, (x, tt)) => (2000 - Z.of_nat(x - y) - Z.of_nat(y - x))).

Definition example3' :=
  forAll arb (fun (x: nat)  =>
  forAll (gen x) (fun (y: nat)  =>
  test2 x y)).

#[local] Instance showUnit : Show unit :=
  {| show _ := "()" |}.

Fixpoint toMonad (C : Ctx) (cprop: CProp C) : ⟦C⟧ -> Checker :=
  match cprop with
  | @ForAll A C name gen mut shr pri cprop' =>
    fun env =>
    forAllShrinkShow (gen env) (shr env) (pri env) (fun a => toMonad (A · C) cprop' (a, env))
  | @ForAllMaybe A C name gen mut shr pri cprop' =>
    fun env =>
    forAllShrinkShowMaybe (gen env) (shr env) (pri env) (fun a => toMonad (A · C) cprop' (a, env))
  | Implies C prop cprop' =>
    fun env =>
    if prop env then toMonad C cprop' env
    else checker None
  | Check C prop =>
    fun env => 
    checker (prop env)
  end.