#lang racket

(require racket/dict)

(require "proplang.rkt")

(provide
 (contract-out
  [shrink-eager (property? dict? dict? . -> . dict?)]
  [shrink-eager-retry (property? dict? dict? . -> . dict?)]))

(define (shrink-eager prop shrinkers env)
  (define (shrink-var env x shrinker)
    (define v (dict-ref env x))
    (let loop ([shrinks (shrinker v)])
      (match shrinks
        ['() v]
        [(cons v vs)
         (if (equal? (check-property prop (dict-set env x v)) 'fail)
             (shrink-var (dict-set env x v) x shrinker)
             (loop vs))])))
  (for/fold ([env env])
            ([x (property-variables prop)])
    (let ([v0 (dict-ref env x)]
          [v1 (shrink-var env x (dict-ref shrinkers x))])
      (if (eq? v0 v1)
          env
          (dict-set env x v1)))))

(define (shrink-eager-retry prop shrinkers env)
  (define new-env (shrink-eager prop shrinkers env))
  (if (eq? env new-env)
      env
      (shrink-eager-retry prop shrinkers env)))