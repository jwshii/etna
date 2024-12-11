#lang racket

(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require data/maybe)
(require property-language)

(define test_prop_SinglePreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_SinglePreserve e) (just #t))
                           )
                          `((e . ,gSized))
                          )))

(define test_prop_MultiPreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_MultiPreserve e) (just #t))
                           )
                          `((e . ,gSized))
                          )))

(provide test_prop_SinglePreserve
         test_prop_MultiPreserve)

