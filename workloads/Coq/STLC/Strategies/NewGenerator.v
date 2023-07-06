 
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From STLC Require Import Impl Spec.

Derive (Arbitrary) for Typ.
Derive (Arbitrary) for Expr.

Inductive bind : Ctx -> nat -> Typ -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

Inductive typing (G : Ctx) : Expr -> Typ -> Prop :=
| TyVar :
    forall x T,
      bind G x T ->
      typing G (Var x) T
| TyBool :
    forall b,
      typing G (Bool b) TBool
| TyAbs :
    forall e T1 T2,
      typing (T1 :: G) e T2 ->
      typing G (Abs T1 e) (TFun T1 T2)
| TyApp :
    forall e1 e2 T1 T2,
      typing G e1 (TFun T1 T2) ->
      typing G e2 T1 ->
      typing G (App e1 e2) T2.


(* Look up in list of backtrack weights *)
Fixpoint get {a: Type} (l : list (nat * a)) (target_key : nat) (default : a): a :=
  match l with
  | [] =>
    (* This branch should never return *)
    default
  | (key, value) :: l' =>
    if Nat.eqb key target_key then
       value
    else get l' target_key default
  end.


#[export] Instance dec_type (t1 t2 : Typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive Arbitrary for Typ.

Fixpoint genVar' (ctx: Ctx) (t: Typ) (p: nat) (r: list nat) : list nat :=
  match ctx with
  | nil => r
  | t'::ctx' =>
      if t = t'? then genVar' ctx' t (p + 1) (p :: r)
      else genVar' ctx' t (p + 1) r
  end.

Fixpoint genZero env tau : G (option Expr) :=
  match tau with
  | TBool =>
      bindGen arbitrary
              (fun b : bool =>
                 returnGen (Some (Bool b)))
  | TFun T1 T2 => 
      bindOpt
        (genZero (T1 :: env) T2)
        (fun e : Expr =>
           returnGen (Some (Abs T1 e)))
  end.

Fixpoint genTyp (s: nat) : G Typ :=
  match s with
  | 0 => ret TBool
  | S s' =>
    let '(boolWeight, funWeight) :=
      get
      [
        (1, (581, 1000-581));
        (2, (807, 1000-807))
      ]
      s
      (0, 0) in
    freq [
      (boolWeight, ret (TBool))
      ;
      (funWeight,
          t1 <- genTyp s';;
          t2 <- genTyp s';;
          ret (TFun t1 t2))
    ]
  end.
  
Fixpoint genExpr env tau (sz: nat) : G (option Expr) :=
  match sz with
  | 0 =>
      backtrack
        [(1, oneOf_ (ret None) (map (fun x => returnGen (Some (Var x))) (genVar' env tau 0 [])))
        ;(1, genZero env tau)] 
  | S sz' =>
      let '(val_weight, app_weight, var_weight) :=
        get
          [
            (1, (40, 662, 722));
            (2, (126, 544, 717));
            (3, (89, 815, 269));
            (4, (465, 589, 432));
            (5, (32, 800, 500))
          ]
          sz
          (0, 0 ,0) in
      backtrack
        [(var_weight, oneOf_ (ret None) (map (fun x => returnGen (Some (Var x))) (genVar' env tau 0 [])))
         ;
        (app_weight,
          bindGen (genTyp 2)
                  (fun T1 : Typ =>
          bindOpt
            (genExpr env (TFun T1 tau) sz')
            (fun e1 : Expr =>
          bindOpt
            (genExpr env T1 sz')
            (fun e2 : Expr =>
               returnGen (Some (App e1 e2))))))
         ; 
         (val_weight,
           match tau with
           | TBool =>
               bindGen arbitrary
                       (fun b : bool =>
                          returnGen (Some (Bool b)))
           | TFun T1 T2 =>
               bindOpt
                 (genExpr (T1 :: env) T2 sz')
                    (fun e : Expr =>
                     returnGen (Some (Abs T1 e)))
              end)]
  end.

Definition gSized := 
    typ <- arbitrary ;;
    genExpr [] typ 5.


Definition test_prop_SinglePreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_SinglePreserve e).

(*! QuickChick test_prop_SinglePreserve. *)
  
Definition test_prop_MultiPreserve :=
  forAllMaybe gSized (fun (e: Expr) =>
    prop_MultiPreserve e).
  
(*! QuickChick test_prop_MultiPreserve. *)

(*
Derive (Arbitrary) for Typ.


(* Fixpoint genTyp (s: nat) : G Typ :=
  match s with
  | 0 => ret TBool
  | S s' => oneOf [
    t1 <- genTyp s' ;;
    t2 <- genTyp s' ;;
    ret (TFun t1 t2) ;
    ret TBool
    ]
  end.
   *)

(* #[export] Instance genArbitrary : GenSized Typ :=
{|
 arbitrarySized x := genTyp x
|}. *)

Definition genTyp (s: nat) : G Typ := arbitrary.

Fixpoint genOne (ctx: Ctx) (t: Typ) : G Expr :=
  match t with
  | TBool =>
    b <- arbitrary ;;
    ret (Bool b)
  | TFun t1 t2 =>
    t' <- genOne (t1 :: ctx) t2 ;;
    ret (Abs t1 t')
  end.


Fixpoint genVar' (ctx: Ctx) (t: Typ) (p: nat) (r: list nat) : list nat :=
  match ctx with
  | nil => r
  | t'::ctx' => if t == t' then genVar' ctx' t (p + 1) (p :: r)
                else genVar' ctx' t (p + 1) r
  end.


Definition genVar (ctx: Ctx) (t: Typ) : list (G Expr) :=
  let positions := genVar' ctx t 0 [] in
  let tf := (fun n => ret (Var n)) in
  map tf positions.


Fixpoint genExactExpr (f: nat) (ctx: Ctx) (t: Typ) : G Expr :=
  match f with
  | O => oneOf_ (genOne ctx t) (genOne ctx t :: genVar ctx t)
  | S f' =>
    let abs : list (G Expr) := match t with
              | TFun t1 t2 =>
                [bindGen (genExactExpr f' (t1 :: ctx) t2) (fun t' => 
                returnGen (Abs t1 t'))]
              | _ => nil
              end in
    let one := genOne ctx t in
    let app := 
      t' <- genTyp f' ;;
      e1 <- genExactExpr f' ctx (TFun t' t) ;;
      e2 <- genExactExpr f' ctx t' ;;
      ret (App e1 e2) in
    let var := genVar ctx t in
    
    oneOf_ one ([one] ++ abs ++ [app] ++ var)
  end.





Definition genExpr (s: nat) : G Expr :=
  t <- genTyp 3 ;;
  genExactExpr s [] t
.

#[export] Instance arbitrarySizedExpr : GenSized Expr :=
{|
  arbitrarySized s := genExpr s
|}.

Definition gTyped := genExpr 5.

Definition test_prop_SinglePreserve :=
  forAll gTyped (fun (e: Expr) =>
    prop_SinglePreserve e).

(* QuickChick test_prop_SinglePreserve. *)

Definition test_prop_MultiPreserve :=
  forAll gTyped (fun (e: Expr) =>
    prop_MultiPreserve e).

(* QuickChick test_prop_MultiPreserve. *)






*)