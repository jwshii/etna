#lang racket

(require data/maybe)
(require "Impl.rkt")
(require "Type.rkt")
(require "Util.rkt")


(define/contract (mtype-check e t)
((maybe/c term?) typ? . -> . boolean?)
    (match e 
        [(just e-prime) (type-check (Empty) e-prime t)]
        [(nothing) #t] ; adding back discards?
    )
)

#| option utils |#

(define (assumes p1 p2)
    (displayln (format "assumes {p1: ~a} {p2: ~a}" p1 p2))
  (match p1
    [(nothing) nothing]
    [(just #f) nothing]
    [(just #t) p2]
    [#t p2]
  )
)

(define/contract (prop_SinglePreserve t)
(term? . -> . (maybe/c boolean?))
    (displayln (format "prop_SinglePreserve {t: ~a}" t))
    (let ([mty (get-typ 40 (Empty) t)]) 
        (displayln (format "mty: ~a" mty))
        (match (just? mty)
            [(nothing) (nothing)]
            [#f (nothing)]
            [(just #f) (nothing)]
            [(just #t) (just (mtype-check (pstep t) (from-just! mty)))]
            [#t (just (mtype-check (pstep t) (from-just! mty)))]
        )
        ; (assumes (just? mty) (just (mtype-check (pstep t) (from-just! mty))))   
    )
)

(define/contract (prop_MultiPreserve t)
(term? . -> . (maybe/c boolean?))
    (let ([mty (get-typ 40 (Empty) t)]) 
        (assumes (just? mty) (just (mtype-check (multi-step pstep t) (from-just! mty))))   
    )
)

(define/contract (size term)
(term? . -> . number?)
    (match term
        [(Abs _ t) (+ 1 (size t))]
        [(App t1 t2) (+ 1 (size t1) (size t2))]
        [(TAbs _ t) (+ 1 (size t))]
        [(TApp t _) (+ 1 (size t))]
        [_ 1]
    )
)

(provide prop_SinglePreserve prop_MultiPreserve)

(module+ test
    (require rackunit)

    (define test-cases 
        (list
            (TApp (TApp (TApp (TAbs (Top) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (Top)) (All (Top) (Arr (TVar 0) (TVar 0)))) (Top))
            ; (TApp (TApp (TAbs (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (App (Abs (Arr (TVar 0) (TVar 0)) (TAbs (Top) (Abs (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (Abs (TVar 0) (Var 0)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (Top))
            ; (TApp (App (Abs (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (TAbs (All (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1)))) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TApp (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0)))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))))) (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))))
            ; (App (TApp (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (All (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 1) (TVar 1))))) (TAbs (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Abs (TVar 0) (Var 0))))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))
            ; (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))))) (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (Abs (TVar 0) (Var 0))))))
            ; (TApp (TApp (TApp (TAbs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (TVar 0) (TAbs (TVar 0) (Abs (TVar 0) (Var 0)))))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Top)) (Top))
            ; (TAbs (All (Top) (All (Arr (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 2) (TVar 2))))) (Abs (TVar 0) (Var 0)))
            ; (TAbs (Top) (TApp (TApp (TAbs (TVar 0) (TAbs (TVar 1) (Abs (TVar 2) (Var 0)))) (TVar 0)) (TVar 0)))
            ; (TApp (TAbs (Top) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Var 0))) (Top))
            ; (App (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (App (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Var 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (TApp (TAbs (Top) (Abs (Arr (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (TVar 0) (Arr (TVar 0) (TVar 0)))) (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (TVar 0) (Abs (TVar 0) (Var 0))))) (Top)))
            ; (TApp (App (Abs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (Arr (TVar 1) (TVar 1)) (Abs (TVar 0) (Var 0)))))))) (TApp (TApp (TAbs (Top) (TAbs (TVar 0) (TAbs (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Abs (TVar 0) (Var 1)))))) (Top)) (Top))) (All (Top) (Arr (TVar 0) (TVar 0))))
        ))
    
    (for ([test-case test-cases])
        (displayln test-case)
        (check-equal? (prop_SinglePreserve test-case) (just #t) "not equal")
    )
)