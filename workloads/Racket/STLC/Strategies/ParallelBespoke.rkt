#lang racket

(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require data/maybe)
(require property-language)

(define test_prop_SinglePreserve
  (lambda (cfg) (parallel-run-loop cfg
                          (property (forall e #:gen gSized)
                                    (equal? (prop_SinglePreserve e) (just #t))) 8)))

(define test_prop_MultiPreserve
  (lambda (cfg) (parallel-run-loop cfg
                          (property (forall e #:gen gSized)
                                    (equal? (prop_MultiPreserve e) (just #t))) 8)))

(provide test_prop_SinglePreserve
         test_prop_MultiPreserve)

;