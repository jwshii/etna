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
       ("rc:test_prop_SinglePreserve"   . ,rc:test_prop_SinglePreserve)
       ("rc:test_prop_MultiPreserve"    . ,rc:test_prop_MultiPreserve)
       ; Proplang properties
        ("pl:test_prop_SinglePreserve"   . ,pl:test_prop_SinglePreserve)
        ("pl:test_prop_MultiPreserve"    . ,pl:test_prop_MultiPreserve)
       )
     )


   (checker-fn (dict-ref props search-key)))
  )