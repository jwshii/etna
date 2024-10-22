#lang racket

(require "../src/Spec.rkt")
(require "../src/Generation.rkt")

(require data/maybe)
(require rackcheck/shrink-tree)

(define (run-generator g sz) (shrink-tree-val (g (current-pseudo-random-generator) sz)))

(require property-language)

(define (run-generators generators n)
  (let ([result (make-hash)]
        [size (inexact->exact (round (log n 2)))])
    (for ([p (in-dict-pairs generators)])
      (dict-set! result (car p) (run-generator (cdr p) size)))
    result))


(struct run-result (time foundbug passed discards counterexample)
  #:transparent)

(define (run-result->json-str rr)
  (format "[|{\"time\": ~a, \"foundbug\": ~a, \"passed\": ~a, \"discards\": ~a, \"counterexample\": \"~a\"}|]"
          (run-result-time rr)
          (if (run-result-foundbug rr) "true" "false")
          (run-result-passed rr)
          (run-result-discards rr)
          (run-result-counterexample rr))
  )

(define (run-loop tests p generators)
  (let ([start (current-inexact-milliseconds)]
        [foundbug #f]
        [passed 0]
        [discards 0]
        [counterexample ""])
    (let loop ([n 1])
      (if (= n tests)
          'passed
          (let ([env (run-generators generators n)])
            (case (check-property p env)
              [(fail) (set! foundbug #t) (set! counterexample (~v env))]
              [(pass) (set! passed (+ 1 passed)) (loop (+ n 1)) ]
              [(discard) (set! discards (+ 1 discards)) (loop (+ n 1))]))))
    (displayln (run-result->json-str (run-result (- (current-inexact-milliseconds) start) foundbug passed discards counterexample)))))


(define test_prop_SinglePreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_SinglePreserve e) (just #t))
                           )
                          `((e . ,gen:term))
                          )))


(define test_prop_MultiPreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_MultiPreserve e) (just #t))
                           )
                          `((e . ,gen:term))
                          )))

(provide test_prop_SinglePreserve test_prop_MultiPreserve)

