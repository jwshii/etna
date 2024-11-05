#lang racket

(require data/maybe)
(require data/monad)

; Typ := Top | TVar Nat | Arr Typ Typ | All Typ Typ
(struct Top () #:transparent)
(struct TVar (n) #:transparent)
(struct Arr (t1 t2) #:transparent)
(struct All (t1 t2) #:transparent)
(define (typ? x)
  (match x
    [(Top) #t]
    [(TVar n) (exact-integer? n)]
    [(Arr t1 t2) (and (typ? t1) (typ? t2))]
    [(All t1 t2) (and (typ? t1) (typ? t2))]
    [_ #f]))

; Term := Var Nat | Abs Typ Term | App Term Term | TAbs Typ Term | TApp Term Typ
(struct Var (n) #:transparent)
(struct Abs (typ term) #:transparent)
(struct App (term1 term2) #:transparent)
(struct TAbs (typ term) #:transparent)
(struct TApp (term typ) #:transparent)
(define (term? x)
  (match x
    [(Var n) (exact-integer? n)]
    [(Abs typ term) (and (typ? typ) (term? term))]
    [(App term1 term2) (and (term? term1) (term? term2))]
    [(TAbs typ term) (and (typ? typ) (term? term))]
    [(TApp term typ) (and (term? term) (typ? typ))]
    [_ #f]))

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
                        All (tshift x ty1) (tshift (+ 1 x) ty2)
                        #|!! tshift_all_no_incr |#
                        #|! 
                            All (tshift x ty1) (tshift x ty2)
                        |#
        )]
    )
)


(define/contract (tshift/correct x typ)
(number? typ? . -> . typ?)
    (match typ
        [(Top) (Top)]
        [(TVar y) (if (<= x y) (TVar (+ 1 y)) (TVar y))]
        [(Arr ty1 ty2) (Arr (tshift/correct x ty1) (tshift/correct x ty2))]
        [(All ty1 ty2) (All (tshift/correct x ty1) (tshift/correct (+ 1 x) ty2))]))



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
                       #|!! shift_abs_no_incr |#
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
        [(Top) (Top)]
        [(TVar y) (#|! |#
                    cond
                    [(< y x) (TVar y)]
                    [(= y x) ty_prime]
                    [else (TVar (- y 1))]
                    #|!! tsubst_tvar_flip |#
                    #|! 
                        cond
                        [(< y x) (TVar (- y 1))]
                        [(= y x) ty_prime]
                        [else (TVar y)]
                    |#
                    #|!! tsubst_tvar_no_shift |#
                    #|! 
                        cond
                        [(< y x) (TVar y)]
                        [(= y x) ty_prime]
                        [else (TVar y)]
                    |#
                    #|!! tsubst_tvar_over_shift |#
                    #|! 
                        cond
                        [(< y x) (TVar (- y 1))]
                        [(= y x) ty_prime]
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


(define/contract (tsubst/correct ty x ty_prime)
(typ? number? typ? . -> . typ?)
    (match ty 
        [(Top) (Top)]
        [(TVar y) (cond
                    [(< y x) (TVar y)]
                    [(= y x) ty_prime]
                    [else (TVar (- y 1))])]
        [(Arr ty1 ty2) (Arr (tsubst/correct ty1 x ty_prime) (tsubst/correct ty2 x ty_prime))]
        [(All ty1 ty2) (All (tsubst/correct ty1 x ty_prime) (tsubst/correct ty2 (+ 1 x) (tshift 0 ty_prime)))]))

(define/contract (subst term x t-prime)
(term? number? term? . -> . term?)
    (match term
        [(Var y) (#|! |#
                  cond 
                  [(< y x) (Var y)]
                  [(= y x) t-prime]
                  [else (Var (- y 1))]
                  #|!! subst_var_flip |#
                  #|!
                    cond 
                    [(< y x) (Var (- y 1))]
                    [(= y x) t-prime]
                    [else (Var y)]
                  |#
                  #|!! subst_var_no_decr |#
                  #|!
                    cond 
                    [(< y x) (Var y)]
                    [(= y x) t-prime]
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

(define/contract (subst/correct term x t-prime)
(term? number? term? . -> . term?)
    (match term
        [(Var y) (cond 
                  [(< y x) (Var y)]
                  [(= y x) t-prime]
                  [else (Var (- y 1))])]
        [(Abs ty1 t2) (Abs ty1 (subst/correct t2 (+ 1 x) (shift 0 t-prime)))] 
        [(App t1 t2) (App (subst/correct t1 x t-prime) (subst/correct t2 x t-prime))]
        [(TAbs ty1 t2) (TAbs ty1 (subst/correct t2 x (shift-typ 0 t-prime)))]
        [(TApp t1 ty2) (TApp (subst/correct t1 x t-prime) ty2)]))


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

(define/contract (subst-typ/correct term x ty)
(term? number? typ? . -> . term?)
    (match term
        [(Var n) (Var n)]
        [(Abs ty1 t2) (Abs (tsubst/correct ty1 x ty) (subst-typ/correct t2 x ty))]
        [(App t1 t2) (App (subst-typ/correct t1 x ty) (subst-typ/correct t2 x ty))]
        [(TAbs ty1 t2) (TAbs (tsubst/correct ty1 x ty) (subst-typ/correct t2 (+ 1 x) (tshift/correct 0 ty)))]
        [(TApp t1 ty2) (TApp (subst-typ/correct t1 x ty) (tsubst/correct ty2 x ty))]
    )
)


#| stepping |#

(define/contract (pstep term)
(term? . -> . (maybe/c term?))
    (match term
        [(Abs ty t) (do [t-prime <- (pstep t)] (just (Abs ty t-prime)))]
        [(App (Abs _ t1) t2) (let* ([t1-prime (from-just t1 (pstep t1))]
                                    [t2-prime (from-just t2 (pstep t2))])
                                    (just (subst t1-prime 0 t2-prime)))]
        [(App t1 t2) (let* ([t1-res (pstep t1)]
                            [t2-res (pstep t2)])
                        (match (list t1-res t2-res)
                            [(list nothing nothing) nothing]
                            [(list mt1 mt2) (let* ([t1-prime (from-just t1 t1-res)]
                                                   [t2-prime (from-just t2 t2-res)])
                                                    (just (App t1-prime t2-prime)))]))]
        [(TAbs ty t) (do [t-prime <- (pstep t)] (just (TAbs ty t-prime)))]
        [(TApp (TAbs _ t) ty) (let* ([t-prime (from-just t (pstep t))])
                                    (just (subst-typ t-prime 0 ty)))]
        [(TApp t ty) (do [t-prime <- (pstep t)] (just (TApp t-prime ty)))] 
        [_ nothing]
    )
)

(define/contract (pstep/correct term)
(term? . -> . (maybe/c term?))
    (match term
        [(Abs ty t) (do [t-prime <- (pstep/correct t)] (just (Abs ty t-prime)))]
        [(App (Abs _ t1) t2) (let* ([t1-prime (from-just t1 (pstep/correct t1))]
                                    [t2-prime (from-just t2 (pstep/correct t2))])
                                    (just (subst/correct t1-prime 0 t2-prime)))]
        [(App t1 t2) (let* ([t1-res (pstep/correct t1)]
                            [t2-res (pstep/correct t2)])
                        (match (list t1-res t2-res)
                            [(list nothing nothing) nothing]
                            [(list mt1 mt2) (let* ([t1-prime (from-just t1 t1-res)]
                                                   [t2-prime (from-just t2 t2-res)])
                                                    (just (App t1-prime t2-prime)))]))]
        [(TAbs ty t) (do [t-prime <- (pstep/correct t)] (just (TAbs ty t-prime)))]
        [(TApp (TAbs _ t) ty) (let* ([t-prime (from-just t (pstep/correct t))])
                                    (just (subst-typ/correct t-prime 0 ty)))]
        [(TApp t ty) (do [t-prime <- (pstep/correct t)] (just (TApp t-prime ty)))] 
        [_ nothing]
    )
)


; (trace tshift)
; (trace shift)
; (trace shift-typ)
; (trace tsubst)
; (trace subst)
; (trace subst-typ)
; (trace pstep)



(provide 
    term?
    Var
    Abs
    App
    TAbs
    TApp
    
    typ?
    Top
    TVar
    Arr
    All

    tshift
    tshift/correct
    shift
    shift-typ
    tsubst
    tsubst/correct
    subst
    subst-typ
    pstep
    pstep/correct
)