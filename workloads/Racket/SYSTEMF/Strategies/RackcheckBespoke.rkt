#lang racket

(require "../src/impl.rkt")
(require "../src/spec.rkt")
(require rackcheck)
(require data/maybe)


(define gen:term
  (let ([size 4])
    (gen:bind (gen:exact-typ size (Empty)) 
    (lambda (ty) (gen:exact-term size Empty ty)))))
    



(define test_prop_SinglePreserve
  (property prop_SinglePreserve ([e gen:term])
            (equal? (prop_SinglePreserve e) (just #t)))
)


(define test_prop_MultiPreserve
  (property prop_MultiPreserve ([e gen:term])
            (equal? (prop_MultiPreserve e) (just #t)))
)

(provide test_prop_SinglePreserve test_prop_MultiPreserve)

