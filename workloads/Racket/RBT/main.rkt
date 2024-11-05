#lang racket/base

(module+ main
  (require racket/cmdline)
  (require rackcheck)
  (require racket/dict)
  (require (prefix-in rc: "Strategies/RackcheckBespoke.rkt"))
  (require (prefix-in pl: "Strategies/ProplangBespoke.rkt"))
  (command-line
   #:program "rackcheck-bespoke"
   #:args info

   (define property (list-ref info 0))
   (define strategy-longform (list-ref info 1))
   (define strategy (case strategy-longform
                      [("RackcheckBespoke" "rc") "rc"]
                      [("ProplangBespoke" "pl") "pl"]
                      (else (error "Unknown strategy"))))

   (define search-key (string-append strategy ":" property))
   ; Dynamically load the property from the strategy file

   (define tests 4000000)
   (define config (make-config #:tests tests #:deadline (+ (current-inexact-milliseconds) (* 240 1000))))

   (define (check-rackcheck-property p) (check-property config p))
   (define (check-tartarus-property p) (p tests))

   (define checker-fn (case strategy
                        [("rc") check-rackcheck-property]
                        [("pl") check-tartarus-property]
                        (else (error "Unknown strategy"))))

   (define props
     `(
       ; Rackcheck properties
       ("rc:test_prop_InsertValid"        . ,rc:test_prop_InsertValid)
       ("rc:test_prop_DeleteValid"        . ,rc:test_prop_DeleteValid)
       ("rc:test_prop_InsertPost"         . ,rc:test_prop_InsertPost)
       ("rc:test_prop_DeletePost"         . ,rc:test_prop_DeletePost)
       ("rc:test_prop_InsertModel"        . ,rc:test_prop_InsertModel)
       ("rc:test_prop_DeleteModel"        . ,rc:test_prop_DeleteModel)
       ("rc:test_prop_InsertInsert"       . ,rc:test_prop_InsertInsert)
       ("rc:test_prop_InsertDelete"       . ,rc:test_prop_InsertDelete)
       ("rc:test_prop_DeleteInsert"       . ,rc:test_prop_DeleteInsert)
       ("rc:test_prop_DeleteDelete"       . ,rc:test_prop_DeleteDelete)
       ; Proplang properties
       ("pl:test_prop_InsertValid"        . ,pl:test_prop_InsertValid)
       ("pl:test_prop_DeleteValid"        . ,pl:test_prop_DeleteValid)
       ("pl:test_prop_InsertPost"         . ,pl:test_prop_InsertPost)
       ("pl:test_prop_DeletePost"         . ,pl:test_prop_DeletePost)
       ("pl:test_prop_InsertModel"        . ,pl:test_prop_InsertModel)
       ("pl:test_prop_DeleteModel"        . ,pl:test_prop_DeleteModel)
       ("pl:test_prop_InsertInsert"       . ,pl:test_prop_InsertInsert)
       ("pl:test_prop_InsertDelete"       . ,pl:test_prop_InsertDelete)
       ("pl:test_prop_DeleteInsert"       . ,pl:test_prop_DeleteInsert)
       ("pl:test_prop_DeleteDelete"       . ,pl:test_prop_DeleteDelete)
       )
     )


   (checker-fn (dict-ref props search-key)))
  )