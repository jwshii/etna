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

#| shifting and substitution |#

(define typ? (lambda (x) (or (Top? x) (TVar? x) (Arr? x) (All? x))))
(define term? (lambda (x) (or (Var? x) (Abs? x) (App? x) (TAbs? x) (TApp? x))))

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

(define/contract (shiftTyp x term)
(number? term? . -> . term?)
    (match term
        [(Var n) (Var n)]
        [(Abs ty1 t2) (Abs (tshift x ty1) (shiftTyp x t2))]
        [(App t1 t2) (App (shiftTyp x t1) (shiftTyp x t2))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs (tshift x ty1) (shiftTyp (+ 1 x) t2)
                        #|!! shift_typ_tabs_no_incr |#
                        #|!
                            TAbs (tshift x ty1) (shiftTyp x t2)
                        |#
        )]
        [(TApp t1 ty2) (TApp (shiftTyp x t1) (tshift x ty2))]
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

(define/contract (subst term x t_prime)
(term? number? term? . -> . term?)
    (match term
        [(Var y) (#|! |#
                  cond 
                  [(< y x) (Var y)]
                  [(= y x) (t_prime)]
                  [else (Var (- y 1))]
                  #|!! subst_var_flip |#
                  #|!
                    cond 
                    [(< y x) (Var (- y 1))]
                    [(= y x) (t_prime)]
                    [else (Var y)]
                  |#
                  #|!! subst_var_no_decr |#
                  #|!
                    cond 
                    [(< y x) (Var y)]
                    [(= y x) (t_prime)]
                    [else (Var y)]
                  |#
        )]
        [(Abs ty1 t2) (#|! |#
                       Abs ty1 (subst t2 (+ 1 x) (shift 0 t_prime))
                       #|!! subst_abs_no_shift |#
                       #|!
                            Abs ty1 (subst t2 (+ 1 x) t_prime)
                       |#
                       #|!! subst_abs_no_incr |#
                       #|!
                            Abs ty1 (subst t2 x (shift 0 t_prime))
                       |#
        )] 
        [(App t1 t2) (App (subst t1 x t_prime) (subst t2 x t_prime))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs ty1 (subst t2 x (shiftTyp 0 t_prime))
                        #|!! subst_tabs_no_shift |#
                        #|! 
                             TAbs ty1 (subst t2 x t_prime)
                        |#

        )]
        [(TApp t1 ty2) (TApp (subst t1 x t_prime) ty2)]
    )
)

(define/contract (substTyp term x ty)
(term? number? typ? . -> . term?)
    (match term
        [(Var n) (Var n)] #| not sure about the matching here |#
        [(Abs ty1 t2) (Abs (tsubst ty1 x ty) (substTyp t2 x ty))]
        [(App t1 t2) (App (substTyp t1 x ty) (substTyp t2 x ty))]
        [(TAbs ty1 t2) (#|! |#
                        TAbs (tsubst ty1 x ty) (substTyp t2 (+ 1 x) (tshift 0 ty))
                        #|!! subst_typ_tabs_no_incr |#
                        #|! 
                             TAbs (tsubst ty1 x ty) (substTyp t2 x (tshift 0 ty))
                        |#
                        #|!! subst_typ_tabs_no_shift |#
                        #|! 
                             TAbs (tsubst ty1 x ty) (substTyp t2 (+ 1 x) ty)
                        |#
        )]
        [(TApp t1 ty2) (TApp (substTyp t1 x ty) (tsubst ty2 x ty))]
    )
)

(define (from-maybe a1 a2)
    (match a2
        [(just v) v]
        [(nothing) a1]
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
                                    (just (substTyp t-prime 0 ty)))]
        [(TApp t ty) (do [t-prime <- (pstep t)] (just (TApp t-prime ty)))] ; not sure!
        [_ nothing]
    )
)
