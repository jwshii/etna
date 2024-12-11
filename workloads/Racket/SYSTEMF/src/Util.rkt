#lang racket

(require data/maybe)
(require racket/trace)
(require (only-in "Impl.rkt" term? typ? Top TVar Arr All Var Abs App TAbs TApp  tshift/correct))

; Env := Empty | EVar Env Typ | EBound Env Typ
(struct Empty () #:transparent)
(struct EVar (env typ) #:transparent)
(struct EBound (env typ) #:transparent)
(define env? (lambda (x) (or (Empty? x) (EVar? x) (EBound? x))))

#| context |#

(define/contract (get-bound e x)
(env? number? . -> . (maybe/c typ?))
    (match e
        [(Empty) (nothing)]
        [(EVar e-prime _) (get-bound e-prime x)]
        [(EBound e-prime ty) 
            (match (match x
                    [0 (just ty)]
                    [_ (get-bound e-prime (- x 1))])
                [(just ty) (just (tshift/correct 0 ty))]
                [(nothing) (nothing)]
            )
        ]
    )
)


(define/contract (get-var e x)
(env? number? . -> . (maybe/c typ?))
    (match e
        [(Empty) (nothing)]
        [(EBound e-prime _) (match (get-var e-prime x)
                                [(just ty) (just (tshift/correct 0 ty))]
                                [(nothing) (nothing)]
                            )]
        [(EVar e-prime ty) (match x
                                [0 (just ty)]
                                [_ (get-var e-prime (- x 1))]
                            )]
    )
)


#| well-formedness |#

(define/contract (wf-typ e ty)
(env? typ? . -> . boolean?)
    (match ty 
        [(Top) #t]
        [(TVar x) (just? (get-bound e x))]
        [(Arr ty1 ty2) (and (wf-typ e ty1) (wf-typ e ty2))]
        [(All ty1 ty2) (and (wf-typ e ty1) (wf-typ (EBound e ty1) ty2))]
    )
)

(define/contract (wf-term e t)
(env? term? . -> . boolean?)
    (match t 
        [(Var x) (just? (get-var e x))]
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


(define/contract (multi-step step e)
((term? . -> . (maybe/c term?)) term? . -> . (maybe/c term?))
    (match (step e)
        [(nothing) (just e)]
        [(just e-prime) (multi-step step e-prime)]
    )
)

(define/contract (is-nf t)
(term? . -> . boolean?)
    (match t
    [(Var _) #t]
    [(Abs _ t) is-nf t]
    [(App (Abs _ _) _) #f]
    [(App t1 t2) (and (is-nf t1) (is-nf t2))]
    [(TAbs _ t) is-nf t]
    [(TApp (TAbs _ _) _) #f]
    [(TApp t _) is-nf t]
    )
)

; (trace get-bound)
; (trace get-var)
; (trace wf-typ)
; (trace wf-term)
; (trace wf-env)
; (trace ctx-app)
; (trace multi-step)
; (trace is-nf)

(provide 
    env?
    Empty
    EVar
    EBound

    get-bound
    get-var

    wf-typ
    wf-term
    wf-env
    
    ctx-app
    multi-step
    is-nf
    
    ctx?
    Hole
    AppFun
    AppArg
    TypeFun
)