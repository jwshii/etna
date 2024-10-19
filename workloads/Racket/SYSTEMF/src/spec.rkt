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
  (match p1
    [(nothing) nothing]
    [(just #f) nothing]
    [(just #t) p2]
    [#t p2]
    )
  )

(define/contract (prop_SinglePreserve t)
  (term? . -> . (maybe/c boolean?))
  (let ([mty (get-typ 40 (Empty) t)])
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
     ; (TApp (TApp (TApp (TAbs (Top) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (Top)) (All (Top) (Arr (TVar 0) (TVar 0)))) (Top))
     ; (TApp (TAbs (Top) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Var 0))) (Top))
     ; (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))))) (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (Abs (TVar 0) (Var 0))))))
     ; (TAbs (All (Top) (All (Arr (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 2) (TVar 2))))) (Abs (TVar 0) (Var 0)))
     ; (TApp (TApp (TAbs (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (App (Abs (Arr (TVar 0) (TVar 0)) (TAbs (Top) (Abs (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (Abs (TVar 0) (Var 0)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (Top))
     ; (TApp (App (Abs (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (TAbs (All (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1)))) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TApp (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0)))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))))) (Arr (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))))
     ; (App (TApp (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (All (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 1) (TVar 1))))) (TAbs (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Abs (TVar 0) (Var 0))))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))
     ; (TApp (TApp (TApp (TAbs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (TVar 0) (TAbs (TVar 0) (Abs (TVar 0) (Var 0)))))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Top)) (Top))
     ; (TAbs (Top) (TApp (TApp (TAbs (TVar 0) (TAbs (TVar 1) (Abs (TVar 2) (Var 0)))) (TVar 0)) (TVar 0)))
     ; (App (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (App (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Var 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (TApp (TAbs (Top) (Abs (Arr (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (TVar 0) (Arr (TVar 0) (TVar 0)))) (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (TVar 0) (Abs (TVar 0) (Var 0))))) (Top)))
     ; (TApp (App (Abs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (Arr (TVar 1) (TVar 1)) (Abs (TVar 0) (Var 0)))))))) (TApp (TApp (TAbs (Top) (TAbs (TVar 0) (TAbs (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Abs (TVar 0) (Var 1)))))) (Top)) (Top))) (All (Top) (Arr (TVar 0) (TVar 0))))
     ; (TApp (TApp (TApp (TAbs (Top) (TAbs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (TVar 1) (TAbs (Arr (All (TVar 2) (Arr (TVar 0) (TVar 0))) (All (TVar 0) (Arr (TVar 0) (TVar 0)))) (TAbs (TVar 1) (TAbs (Arr (TVar 0) (Arr (TVar 1) (TVar 1))) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0))))))))) (Top)) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Top))
     ; (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (App (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Var 2)))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Var 1))) (All (Top) (Arr (TVar 0) (TVar 0)))))))
     ; (Abs (Arr (All (Top) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))
     ; (TApp (TApp (App (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (Arr (Arr (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1)))) (Abs (TVar 0) (Var 0)))))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Var 0)))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))))
     ; (TAbs (Top) (Abs (TVar 0) (Abs (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (Var 0))))
     ; (TApp (App (Abs (All (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 1) (TVar 1)))) (TAbs (All (All (Top) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (Arr (TVar 1) (TVar 1))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (Abs (TVar 1) (Var 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (All (All (Top) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (Arr (TVar 1) (TVar 1))))))
     ; (TApp (App (App (TApp (TAbs (Top) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Arr (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (Abs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Var 0))))))))) (Top)) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Var 0)))) (All (Top) (Arr (TVar 0) (TVar 0))))
     ; (App (TApp (TAbs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TApp (TAbs (Arr (TVar 0) (TVar 0)) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Var 1)))) (Arr (TVar 0) (TVar 0)))) (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TApp (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (TVar 0) (Abs (TVar 0) (Var 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (Top)))
     ; (TApp (TApp (TAbs (Top) (TAbs (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (Abs (All (Top) (Arr (TVar 0) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1))))) (Abs (All (Top) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))))))) (Top)) (Arr (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))))
     ; (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (TAbs (Top) (Abs (TVar 0) (Var 0))))
     ; (TApp (App (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (All (All (Top) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (Abs (All (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Arr (Arr (TVar 0) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (TVar 0) (Abs (TVar 0) (Var 0)))))))) (TAbs (Top) (Abs (TVar 0) (Var 0)))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (All (All (Top) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))))
    ;  (TApp (TApp (TAbs (Top) (App (Abs (Arr (TVar 0) (TVar 0)) (TAbs (Arr (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Abs (TVar 0) (Var 1)))))))) (Abs (TVar 0) (Var 0)))) (Top)) (Arr (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (Top) (Arr (TVar 0) (TVar 0)))))
    ;  (TApp (TAbs (Top) (TAbs (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (Abs (All (TVar 1) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1)))) (TAbs (Arr (TVar 0) (TVar 0)) (TAbs (TVar 2) (Abs (TVar 0) (Var 0))))))) (Top))
    ;  (TAbs (Top) (Abs (TVar 0) (TApp (TAbs (Arr (TVar 0) (TVar 0)) (Var 0)) (Arr (TVar 0) (TVar 0)))))
    ;  (App (TApp (TAbs (Top) (Abs (All (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0))))))) (Top)) (App (TApp (TAbs (Top) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (TVar 0) (Arr (TVar 0) (TVar 0))))) (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Abs (TVar 0) (Var 1)))))) (Top)) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))))
    ;  (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (TAbs (All (Arr (TVar 1) (TVar 1)) (Arr (TVar 1) (TVar 1))) (Abs (Arr (TVar 1) (TVar 1)) (Abs (TVar 0) (Var 0))))))
    ;  (App (Abs (All (Top) (Arr (TVar 0) (TVar 0))) (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Arr (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))
    ;  (Abs (All (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (All (Top) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 2) (TVar 2))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))
    ;  (TApp (App (Abs (Arr (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (All (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1))))) (Abs (All (Top) (Arr (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TAbs (Top) (Abs (TVar 0) (Var 0))))))) (All (Top) (Arr (TVar 0) (TVar 0))))) (TApp (TApp (TAbs (Top) (TAbs (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Abs (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 0) (TVar 0)))) (TAbs (Top) (Abs (TVar 0) (Var 0)))))) (Top)) (All (Top) (Arr (TVar 0) (TVar 0))))) (All (All (All (All (Top) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Top) (Arr (TVar 1) (TVar 1)))) (All (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1))))))
    ;  (TApp (TAbs (All (Top) (Arr (TVar 0) (TVar 0))) (TAbs (Top) (App (Abs (Arr (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0))) (Abs (TVar 0) (Var 0))))) (All (Top) (Arr (TVar 0) (TVar 0))))
    ;  (TApp (TApp (TApp (TAbs (Top) (TAbs (TVar 0) (TAbs (TVar 0) (Abs (All (TVar 0) (Arr (TVar 0) (TVar 0))) (TAbs (All (Arr (All (Top) (Arr (TVar 0) (TVar 0))) (All (TVar 2) (Arr (TVar 0) (TVar 0)))) (Arr (TVar 0) (TVar 0))) (TAbs (TVar 3) (Abs (TVar 0) (Var 0)))))))) (Top)) (Top)) (Top))
    ;  (TAbs (Top) (Abs (TVar 0) (TAbs (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (TAbs (Arr (TVar 0) (TVar 0)) (Abs (TVar 1) (Var 0))))))
     ))

  (for ([test-case test-cases])
    (check-equal? (prop_SinglePreserve test-case) (just #t) "not equal")
    )
  )