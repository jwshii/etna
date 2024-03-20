#lang racket/base

(require "src/impl.rkt")
(require "src/spec.rkt")
(require "Strategies/RackcheckBespoke.rkt")
(require rackcheck)
(require racket/cmdline)
(require rebellion/collection/association-list)

(define config (make-config #:tests 20000 #:deadline (+ (current-inexact-milliseconds) (* 240 1000))))

(define props
    (association-list "test_prop_InsertValid" test_prop_InsertValid
                      "test_prop_DeleteValid" test_prop_DeleteValid                      
                      "test_prop_InsertPost" test_prop_InsertPost
                      "test_prop_DeletePost" test_prop_DeletePost                    
                      "test_prop_InsertModel" test_prop_InsertModel
                      "test_prop_DeleteModel" test_prop_DeleteModel                     
                      "test_prop_InsertInsert" test_prop_InsertInsert
                      "test_prop_InsertDelete" test_prop_InsertDelete   
                      "test_prop_DeleteInsert" test_prop_DeleteInsert
                      "test_prop_DeleteDelete" test_prop_DeleteDelete                      
    )
)

(module+ main
    (command-line
      #:program "rackcheck-bespoke"
      #:args info
      (check-property config (vector-ref (association-list-ref props (list-ref info 0)) 0)))
)