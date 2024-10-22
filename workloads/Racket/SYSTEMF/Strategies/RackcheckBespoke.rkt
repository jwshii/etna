#lang racket

(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require rackcheck)
(require data/maybe)

(define test_prop_SinglePreserve
  (property prop_SinglePreserve ([e gen:term])
            (equal? (prop_SinglePreserve e) (just #t))))

(define test_prop_MultiPreserve
  (property prop_MultiPreserve ([e gen:term])
            (equal? (prop_MultiPreserve e) (just #t))))

(provide test_prop_SinglePreserve test_prop_MultiPreserve)

