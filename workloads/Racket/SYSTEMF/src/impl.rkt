#lang racket

(provide (all-defined-out))

(require data/maybe)
(require data/monad)

(struct Top () #:transparent)
(struct TVar (n) #:transparent)
(struct Arr (t1 t2) #:transparent)
(struct All (t1 t2) #:transparent)

(struct Var (n) #:transparent)
(struct Abs (typ term) #:transparent)
(struct App (term1 term2) #:transparent)
(struct TAbs (typ term) #:transparent)
(struct TApp (term typ) #:transparent)


(define typ? (lambda (x) (or (Top? x) (TVar? x) (Arr? x) (All? x))))
(define term? (lambda (x) (or (Var? x) (Abs? x) (App? x) (TAbs? x) (TApp? x))))
(define env? (lambda (x) (or (Empty? x) (EVar? x) (EBound? x))))

#| option utils |#

(define (assumes p1 p2)
  (match p1
    [(nothing) nothing]
    [(just #f) nothing]
    [(just #t) p2]
    [#t p2]
  )
)

(define (return x)
  (match x
    [(nothing) (nothing)]
    [(just x) (just x)]
    [_ (just x)]
    )
)

(define (is-just a)
    (match a 
        [(just _) #t]
        [(nothing) #f]
    )
)

(define (from-maybe a1 a2)
    (match a2
        [(just v) v]
        [(nothing) a1]
    )
)

(define/contract (from-just a)
((maybe/c any/c) . -> . any/c)
    (match a
        [nothing (raise "from-just received a nothing" #t)]
        [(just a-prime) (a-prime)]
    )
)

(define (apply-maybe f x)
  (match x
    [(just x) (f x)]
    [(nothing) (nothing)]
  )
)

#| context |#

(struct Empty () #:transparent)
(struct EVar (env typ) #:transparent)
(struct EBound (env typ) #:transparent)

(define/contract (get-var e x)
(env? number? . -> . (maybe/c typ?))
    (match e
        [(Empty) (nothing)]
        [(EBound e-prime _) (match (get-var e-prime x)
                                [(just ty) (tshift 0 ty)]
                                [(nothing) (nothing)]
                            )]
        [(EVar e-prime ty) (match x
                                [0 (just ty)]
                                [_ (get-var e-prime (- x 1))]
                            )]
    )
)

(define/contract (get-bound e x)
(env? number? . -> . (maybe/c typ?))
    (match e
        [(Empty) nothing]
        [(EVar e-prime ty) (get-bound e-prime x)]
        [(EBound e-prime ty) 
            (match (match x
                    [0 (just ty)]
                    [_ (get-bound e-prime (- x 1))]    
                    )
                [(just ty) (tshift 0 ty)]
                [(nothing) (nothing)]
            )
        ]
    )
)

#| type |#

(define/contract (get-typ ctx e)
(env? term? . -> . (maybe/c typ?))
    (match e 
        [(Var x) (if (wf-env e) (get-var e x)(nothing))]
        [(Abs ty1 t2) (do [ty2 <- (get-typ (EVar e ty1) t2)] (return (Arr ty1 ty2)))]
        [(App t1 t2) (do [ty1 <- (get-typ e t1)]
                            (do [(All ty11 ty12) <- (promote-TVar e ty1)]
                                (do [ty2 <- (get-typ e t2)]
                                    (if (sub-check e ty2 ty11)
                                        (return ty12)
                                        (nothing)
                                    )
                                )
                            ))]
        [(TAbs ty1 t2) (do [ty2 <- (get-typ (EBound e ty1) t2)] (return (All ty1 ty2)))]
        [(TApp t1 ty2)    
                        (do [ty1 <- (get-typ e t1)]
                            (do [(All ty11 ty12) <- (promote-TVar e ty1)]
                                (if (sub-check e ty2 ty11) (return (tsubst ty12 0 ty2)) (nothing) )
                            ))]
    )
)

(define/contract (type-check e t ty)
(env? term? typ? . -> . boolean?)
    (match (get-typ e t)
        [(just ty-prime) #f] 
        [nothing #f]
    )
)

(define/contract (promote-TVar e typ)
(env? typ? . -> . (maybe/c typ?))
    (match typ
       ; [(ty-prime) (if (or (wf-env e) (wf-typ e typ)) (nothing) (return typ))] ; what to return if it is well formed?
        [(TVar n) (do [ty-prime <- (get-bound e n)] (promote-TVar e ty-prime))]
    )
)

(define/contract (sub-check e ty1 ty2)
(env? typ? typ? . -> . boolean?)
    (match (list ty1 ty2)
        [(list ty1 (Top)) (and (wf-env e) (wf-typ e ty1))]
        [(list (TVar x1) ty2) (if (equal? ty1 ty2)
                                (and (wf-env e) (wf-typ e ty1))
                                (match (get-bound e x1)
                                        [(just ty-prime) (sub-check e ty-prime ty2)]
                                        [nothing #f]
                            
                                ))]
        [(list (Arr s1 s2) (Arr t1 t2)) (and (sub-check e t1 s1) (sub-check e s2 t2))]
        [(list (All s1 s2) (All t1 t2)) (and (sub-check e t1 s1) (sub-check (EBound e t1) s2 t2))]
        [(list _ _) #f]
    )
)

#| well-formedness |#

(define/contract (wf-typ e ty)
(env? typ? . -> . boolean?)
    (match ty 
        [(Top) #t]
        [(TVar x) (is-just (get-bound e x))]
        [(Arr ty1 ty2) (and (wf-typ e ty1) (wf-typ e ty2))]
        [(All ty1 ty2) (and (wf-typ e ty1) (wf-typ (EBound e ty1) ty2))]
    )
)

(define/contract (wf-term e t)
(env? term? . -> . boolean?)
    (match t 
        [(Var x) (is-just (get-var e x))]
        [(Abs ty1 t2) (and (wf-typ e ty1) (wf-term (EVar e ty1) t2))]
        [(App t1 t2) (and (wf-term e t1) (wf-term e t2))]
        [(TAbs ty1 t2) (and (wf-typ e ty1) (wf-term (EBound e ty1) t2))]
        [(TApp t1 ty2) (and (wf-term e t1) (wf-typ e ty2))]
    )
)

(define/contract (wf-env e)
(env? . -> . boolean?)
    (match e
        [(Empty) #t]
        [(EVar e ty) (and (wf-typ e ty) (wf-env e))]
        [(EBound e ty) (and (wf-typ e ty) (wf-env e))]
    )
)

#| reduction |#

(struct Hole () #:transparent)
(struct AppFun (ctx t) #:transparent)
(struct AppArg (ctx t) #:transparent)
(struct TypeFun (ctx typ) #:transparent)

(define ctx? (lambda (x) (or (Hole? x) (AppFun? x) (AppArg? x) (TypeFun? x))))

(define/contract (ctx-app c t)
(ctx? term? . -> . term?)
    (match c
        [(Hole) t]
        [(AppFun c-prime t-prime) (App (ctx-app c-prime t) t-prime)]
        [(AppArg c-prime t-prime) (App t-prime (ctx-app c-prime t))]
        [(TypeFun c-prime ty) (TApp (ctx-app c-prime t) ty)]
    )
)


#| shifting and substitution |#

(define/contract (tshift x typ)
(number? typ? . -> . typ?)
    (match typ
        [(Top) (Top)]
        [(TVar y) (#|! |#
                     if (<= x y) (TVar (+ 1 y)) (TVar y)
                     #|!! tshift_tvar_all |#
                     #|!
                         TVar (+ 1 y)
                     |#
                     #|!! tshift_tvar_no_incr |#
                     #|!
                         TVar y
                     |#
        )]
        [(Arr ty1 ty2) (Arr (tshift x ty1) (tshift x ty2))]
        [(All ty1 ty2) (#|! |#
                        All (tshift x ty1) (tshift (+ 1 x) (ty2))
                        #|!! tshift_all_no_incr |#
                        #|! 
                            All (tshift x ty1) (tshift x ty2)
                        |#
        )]
    )
)

(define/contract (shift x term)
(number? term? . -> . term?)
    (match term
        [(Var y) (#|! |#
                  if (<= x y) (Var (+ 1 y)) (Var y)
                  #|!! shift_var_all |#
                  #|! 
                       Var (+ 1 y)
                  |#
                  #|!! shift_var_no_incr |#
                  #|! 
                       Var y
                  |#
        )]
        [(Abs ty1 t2) (#|! |#
                       Abs ty1 (shift (+ 1 x) t2)
                       #|!! shift_abs_no incr |#
                       #|! 
                            Abs ty1 (shift x t2)
                       |#
        )]
        [(App t1 t2) (App (shift x t1) (shift x t2))]
        [(TAbs ty1 t2) (TAbs ty1 (shift x t2))]
        [(TApp t1 ty2) (TApp (shift x t1) ty2)]
    )
)

(define/contract (shift-typ x term)
(number? term? . -> . term?)
    (match term
        [(Var n) (Var n)]
        [(Abs ty1 t2) (Abs (tshift x ty1) (shift-typ x t2))]
        [(App t1 t2) (App (shift-typ x t1) (shift-typ x t2))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs (tshift x ty1) (shift-typ (+ 1 x) t2)
                        #|!! shift_typ_tabs_no_incr |#
                        #|!
                            TAbs (tshift x ty1) (shift-typ x t2)
                        |#
        )]
        [(TApp t1 ty2) (TApp (shift-typ x t1) (tshift x ty2))]
    )
)

(define/contract (tsubst ty x ty_prime)
(typ? number? typ? . -> . typ?)
    (match ty 
        [(TVar y) (#|! |#
                    cond
                    [(< y x) (TVar y)]
                    [(= y x) (ty_prime)]
                    [else (TVar (- y 1))]
                   #|!! tsubst_tvar_flip |#
                   #|! 
                        cond
                        [(< y x) (TVar (- y 1))]
                        [(= y x) (ty_prime)]
                        [else (TVar y)]
                   |#
                   #|!! tsubst_tvar_no_shift |#
                   #|! 
                        cond
                        [(< y x) (TVar y)]
                        [(= y x) (ty_prime)]
                        [else (TVar y)]
                   |#
                   #|!! tsubst_tvar_over_shift |#
                   #|! 
                        cond
                        [(< y x) (TVar (- y 1))]
                        [(= y x) (ty_prime)]
                        [else (TVar (- y 1))]
                   |#
        )]
        [(Arr ty1 ty2) (Arr (tsubst ty1 x ty_prime) (tsubst ty2 x ty_prime))]
        [(All ty1 ty2) (#|! |#
                        All (tsubst ty1 x ty_prime) (tsubst ty2 (+ 1 x) (tshift 0 ty_prime))
                        #|!! tsubst_all_no_shift |#
                        #|!
                            All (tsubst ty1 x ty_prime) (tsubst ty2 (+ 1 x) ty_prime)
                        |#
        )]
    )
)

(define/contract (subst term x t-prime)
(term? number? term? . -> . term?)
    (match term
        [(Var y) (#|! |#
                  cond 
                  [(< y x) (Var y)]
                  [(= y x) (t-prime)]
                  [else (Var (- y 1))]
                  #|!! subst_var_flip |#
                  #|!
                    cond 
                    [(< y x) (Var (- y 1))]
                    [(= y x) (t-prime)]
                    [else (Var y)]
                  |#
                  #|!! subst_var_no_decr |#
                  #|!
                    cond 
                    [(< y x) (Var y)]
                    [(= y x) (t-prime)]
                    [else (Var y)]
                  |#
        )]
        [(Abs ty1 t2) (#|! |#
                       Abs ty1 (subst t2 (+ 1 x) (shift 0 t-prime))
                       #|!! subst_abs_no_shift |#
                       #|!
                            Abs ty1 (subst t2 (+ 1 x) t-prime)
                       |#
                       #|!! subst_abs_no_incr |#
                       #|!
                            Abs ty1 (subst t2 x (shift 0 t-prime))
                       |#
        )] 
        [(App t1 t2) (App (subst t1 x t-prime) (subst t2 x t-prime))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs ty1 (subst t2 x (shift-typ 0 t-prime))
                        #|!! subst_tabs_no_shift |#
                        #|! 
                             TAbs ty1 (subst t2 x t-prime)
                        |#

        )]
        [(TApp t1 ty2) (TApp (subst t1 x t-prime) ty2)]
    )
)

(define/contract (subst-typ term x ty)
(term? number? typ? . -> . term?)
    (match term
        [(Var n) (Var n)] #| not sure about the matching here |#
        [(Abs ty1 t2) (Abs (tsubst ty1 x ty) (subst-typ t2 x ty))]
        [(App t1 t2) (App (subst-typ t1 x ty) (subst-typ t2 x ty))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs (tsubst ty1 x ty) (subst-typ t2 (+ 1 x) (tshift 0 ty))
                        #|!! subst_typ_tabs_no_incr |#
                        #|! 
                             TAbs (tsubst ty1 x ty) (subst-typ t2 x (tshift 0 ty))
                        |#
                        #|!! subst_typ_tabs_no_shift |#
                        #|! 
                             TAbs (tsubst ty1 x ty) (subst-typ t2 (+ 1 x) ty)
                        |#
        )]
        [(TApp t1 ty2) (TApp (subst-typ t1 x ty) (tsubst ty2 x ty))]
    )
)

#| stepping |#

(define/contract (pstep term)
(term? . -> . (maybe/c term?))
    (match term
        [(Abs ty t) (do [t-prime <- (pstep t)] (just (Abs ty t-prime)))]
        [(App (Abs _ t1) t2) (let* ([t1-prime (from-maybe t1 (pstep t1))]
                                    [t2-prime (from-maybe t2 (pstep t2))])
                                    (just (subst t1-prime 0 t2-prime)))]
        [(App t1 t2) (let* ([t1-res (pstep t1)]
                            [t2-res (pstep t2)])
                        (match (list t1-res t2-res)
                            [(list nothing nothing) nothing]
                            [(list mt1 mt2) (let* ([t1-prime (from-maybe t1 t1-res)]
                                                   [t2-prime (from-maybe t2 t2-res)])
                                                    (just (App t1-prime t2-prime)))]))]
        [(TAbs ty t) (do [t-prime <- (pstep t)] (just (TAbs ty t-prime)))]
        [(TApp (TAbs _ t) ty) (let* ([t-prime (from-maybe t (pstep t))])
                                    (just (subst-typ t-prime 0 ty)))]
        [(TApp t ty) (do [t-prime <- (pstep t)] (just (TApp t-prime ty)))] 
        [_ nothing]
    )
)

(define/contract (multi-step step e)
((term? . -> . (maybe/c term?)) term? . -> . (maybe/c term?))
    (match (step e)
        [nothing (just e)]
        [(just e-prime) (multi-step step e-prime)]
    )
)