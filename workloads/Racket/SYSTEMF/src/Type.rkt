
#lang racket

(require data/maybe)
(require data/monad)
(require racket/trace)
(require "Impl.rkt")
(require "Util.rkt")

#| type |#

(define/contract (type-check e t ty)
  (env? term? typ? . -> . boolean?)
  (match (get-typ (-1) e t)
    [(just ty-p) (sub-check (-1) e ty-p ty)]
    [(nothing) #f]
    )
  )

(define/contract (get-typ fuel e term)
  (number? env? term? . -> . (maybe/c typ?))
  (match term
    [(Var x)
     (if (wf-env e)
         (get-var e x)
         (nothing))]
    [(Abs ty1 t2)
     (do [ty2 <- (get-typ fuel (EVar e ty1) t2)]
       (just (Arr ty1 ty2)))]
    [(App t1 t2)
     (do [ty1 <- (get-typ fuel e t1)]
       (do [(Arr ty11 ty12) <- (promote-TVar fuel e ty1)]
         (do [ty2 <- (get-typ fuel e t2)]
           (if (sub-check fuel e ty2 ty11)
               ty12
               (nothing)))))]
    [(TAbs ty1 t2)
     (do [ty2 <- (get-typ fuel (EBound e ty1) t2)]
       (just (All ty1 ty2)))]
    [(TApp t1 ty2)
     (do [ty1 <- (get-typ fuel e t1)]
       (match (promote-TVar fuel e ty1)
         [(just (All ty11 ty12))
          (do [ty2 <- (promote-TVar fuel e ty2)]
            (if (sub-check fuel e ty2 ty11)
                (just (tsubst ty12 0 ty2))
                (nothing)))]
         [_ (nothing)]
         ))]
    )
  )

(define/contract (promote-TVar fuel e ty)
  (number? env? typ? . -> . (maybe/c typ?))
  (if (equal? fuel 0)
      (nothing)
      (match ty
        [_ #:when (not (and (wf-env e) (wf-typ e ty))) (nothing)]
        [(TVar n)
         (do [ty <- (get-bound e n)]
           (promote-TVar (- fuel 1) e ty))]
        [_  (just ty)]
        )
      )
  )

(define/contract (sub-check fuel e ty1 ty2)
  (number? env? typ? typ? . -> . boolean?)
  (if (eq? fuel 0)
      #f
      (match (list ty1 ty2)
        [(list ty1 (Top)) (and (wf-env e) (wf-typ e ty1))]
        [(list (TVar x1) ty2)
         (if (eq? ty1 ty2)
             (and (wf-env e) (wf-typ e ty1))
             (match (get-bound e x1)
               [(just ty1) (sub-check (- fuel 1) e ty1 ty2)]
               [(nothing) #f]
               )
             )
         ]
        [(list (Arr s1 s2) (Arr t1 t2))
         (and (sub-check (- fuel 1) e t1 s1)
              (sub-check (- fuel 1) e s2 t2))]
        [(list (All s1 s2) (All t1 t2))
         (and (sub-check (- fuel 1) e t1 s1)
              (sub-check (- fuel 1) (EBound e t1) s2 t2))]
        [(list _ _) #f]
        )
      )
  )

(trace type-check)
(trace get-typ)
(trace promote-TVar)
(trace sub-check)

(provide
 type-check
 get-typ
 promote-TVar
 sub-check
 )