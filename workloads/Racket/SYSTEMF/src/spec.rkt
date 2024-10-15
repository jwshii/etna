#lang racket

(require "./impl.rkt")
(require data/maybe)

(define/contract (mtype-check e t)
((maybe/c term?) typ? . -> . boolean?)
    (match e 
        [(just e-prime) (type-check (Empty) e-prime t)]
        [nothing #t] ; adding back discards?
    )
)

(define (prop_SinglePreserve t)
    (let ([mty (get-typ (Empty) t)]) 
        (assumes (is-just mty) (just (mtype-check (pstep t) (from-just mty))))   
    )
)

(define (prop_MultiPreserve t)
    (let ([mty (get-typ (Empty) t)]) 
        (assumes (is-just mty) (just (mtype-check (multi-step pstep t) (from-just mty))))   
    )
)

(define/contract (size-FSub term)
(term? . -> . number?)
    (match term
        [(Abs _ t) (+ 1 (size-FSub t))]
        [(App t1 t2) (+ 1 (size-FSub t1) (size-FSub t2))]
        [(TAbs _ t) (+ 1 (size-FSub t))]
        [(TApp t _) (+ 1 (size-FSub t))]
        [_ 1]
    )
)

(provide prop_SinglePreserve prop_MultiPreserve size-FSub)
