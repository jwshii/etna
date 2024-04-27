#lang racket/base

(module+ main
  (require racket/cmdline)
  (require "src/impl.rkt")
  (require "src/spec.rkt")
  (require rackcheck)
  (require racket/dict)
  (require (prefix-in rc: "Strategies/RackcheckBespoke.rkt"))
  (require (prefix-in pl: "Strategies/ProplangBespoke.rkt"))

  (command-line
   #:program "rackcheck-bespoke"
   #:args info

   (define property (list-ref info 0))
   (define strategy (list-ref info 1))

  (define strategy-longform (case strategy
                      [("RackcheckBespoke" "rc") "RackcheckBespoke"]
                      [("ProplangBespoke" "pl") "ProplangBespoke"]
                      (else (error "Unknown strategy"))))

  (define prop-fn (dynamic-require (string-append "Strategies/" strategy-longform ".rkt") (string->symbol property)))

   ; Dynamically load the property from the strategy file

   (define tests 4000000)
   (define config (make-config #:tests tests #:deadline (+ (current-inexact-milliseconds) (* 240 1000))))

   (define (check-rackcheck-property p) (check-property config p))
   (define (check-tartarus-property p) (p tests))

   (define checker-fn (case strategy-longform
                        [("RackcheckBespoke") check-rackcheck-property]
                        [("ProplangBespoke") check-tartarus-property]
                        (else (error "Unknown strategy"))))

   (checker-fn prop-fn)
  ))