#lang racket
(require "./impl.rkt")
(require "./spec.rkt")
(define test-case-1 (TApp (TApp (TApp (TAbs Top (TAbs (All Top (Arr (TVar 0) (TVar 0))) (TAbs Top (TAbs Top (Abs (TVar 0) (Var 0)))))) Top) (All Top (Arr (TVar 0) (TVar 0)))) Top))

(check-equal? (prop_SinglePreserve test-case-1) (just #t))

; TApp (TApp (TAbs (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (App (Abs (Arr (TVar 0) (TVar 0)) (TAbs Top (Abs (Arr (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (All Top (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) (TAbs Top (Abs (TVar 0) (Var 0)))))) (Abs (TVar 0) (Var 0)))) (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))))) Top

; TApp (App (Abs (All Top (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0)))) (TApp (TAbs (All Top (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 1) (TVar 1)))) (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0))))) (TAbs (All (All Top (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 1) (TVar 1)))) (Arr (TVar 0) (TVar 0))) (TAbs Top (Abs (TVar 0) (Var 0)))))) (All Top (Arr (TVar 0) (TVar 0))))) (TApp (TApp (TAbs (All Top (Arr (TVar 0) (TVar 0))) (TAbs (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (TAbs Top (TAbs (Arr (TVar 0) (TVar 0)) (Abs (TVar 0) (Var 0)))))) (All Top (Arr (TVar 0) (TVar 0)))) (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))))) (Arr (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 1) (TVar 1)))) (All (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))))

; App (TApp (TApp (TAbs (All Top (Arr (TVar 0) (TVar 0))) (TAbs (All Top (Arr (TVar 0) (TVar 0))) (Abs (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (Abs (All Top (All (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 1) (TVar 1))))) (TAbs (Arr (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0))))) (Abs (TVar 0) (Var 0))))))) (All Top (Arr (TVar 0) (TVar 0)))) (All Top (Arr (TVar 0) (TVar 0)))) (Abs (All Top (Arr (TVar 0) (TVar 0))) (TAbs Top (Abs (TVar 0) (Var 0))))

; Abs (Arr (Arr (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0))))) (Arr (All Top (Arr (TVar 0) (TVar 0))) (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))))) (Abs (Arr (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) (Abs (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (TAbs Top (Abs (TVar 0) (Var 0)))))

; TApp (TApp (TApp (TAbs (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0))) (TAbs Top (TAbs (TVar 0) (TAbs (TVar 0) (Abs (TVar 0) (Var 0)))))) (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (TVar 0)))) Top) Top

; TAbs (All Top (All (Arr (TVar 0) (Arr (TVar 0) (TVar 0))) (All (Arr (TVar 0) (TVar 0)) (Arr (TVar 2) (TVar 2))))) (Abs (TVar 0) (Var 0))

; TAbs Top (TApp (TApp (TAbs (TVar 0) (TAbs (TVar 1) (Abs (TVar 2) (Var 0)))) (TVar 0)) (TVar 0))

; TApp (TAbs Top (Abs (All Top (Arr (TVar 0) (TVar 0))) (Var 0))) Top

; App (Abs (Arr (Arr (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0))))) (All Top (Arr (TVar 0) (TVar 0)))) (App (App (Abs (All Top (Arr (TVar 0) (TVar 0))) (Abs (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (Var 0))) (TAbs Top (Abs (TVar 0) (Var 0)))) (App (Abs (All Top (Arr (TVar 0) (TVar 0))) (Abs (All Top (Arr (TVar 0) (TVar 0))) (TAbs Top (Abs (TVar 0) (Var 0))))) (TAbs Top (Abs (TVar 0) (Var 0)))))) (TApp (TAbs Top (Abs (Arr (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All (TVar 0) (Arr (TVar 0) (TVar 0)))) (Arr (All (TVar 0) (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0))))) (TAbs (TVar 0) (Abs (TVar 0) (Var 0))))) Top)

; TApp (App (Abs (All (All Top (Arr (TVar 0) (TVar 0))) (Arr (TVar 0) (Arr (TVar 0) (TVar 0)))) (TAbs (All Top (Arr (TVar 0) (TVar 0))) (Abs (Arr (Arr (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (All Top (Arr (TVar 0) (TVar 0)))) (Arr (Arr (All Top (Arr (TVar 0) (TVar 0))) (All Top (Arr (TVar 0) (TVar 0)))) (All Top (Arr (TVar 0) (TVar 0))))) (TAbs Top (TAbs (Arr (TVar 0) (TVar 0)) (Abs (Arr (TVar 1) (TVar 1)) (Abs (TVar 0) (Var 0)))))))) (TApp (TApp (TAbs Top (TAbs (TVar 0) (TAbs (All (TVar 0) (Arr (TVar 0) (TVar 0))) (Abs (TVar 0) (Abs (TVar 0) (Var 1)))))) Top) Top)) (All Top (Arr (TVar 0) (TVar 0)))
; ))
