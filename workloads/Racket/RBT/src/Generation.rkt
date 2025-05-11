#lang racket


(require "Impl.rkt")
(require rackcheck)

(define (blacken-correct t)
    (match t 
        [(E) (E)]
        [(T c a k v b) (T (B) a k v b)]
    )
)

(define (balance-correct col tl k v tr)
    (match (list col tl k v tr)
        [(list (B) (T (R) (T (R) a x vx b) y vy c) z vz d) 
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) (T (R) a x vx (T (R) b y vy c)) z vz d)
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) a x vx (T (R) (T (R) b y vy c) z vz d)) 
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list (B) a x vx (T (R) b y vy (T (R) c z vz d)))
            (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))]
        [(list rb a x vx b) (T rb a x vx b)]
    )
)

(define (insert-aux kv t)
    (let ([x (first kv)])
     (let([vx (second kv)])
        (match t 
            [(E) (T (R) (E) x vx (E))]
            [(T rb a y vy b) (cond  [(< x y) (balance-correct rb (insert-aux kv a) y vy b)]
                                    [(< y x) (balance-correct rb a y vy (insert-aux kv b))]
                                    [else (T rb a y vx b)])]
        )))
)

(define (insert-correct kv s)
    (blacken-correct (insert-aux kv s))
)

(define gen:kv (gen:tuple gen:natural gen:natural))

(define gen:kvlist (gen:list gen:kv))

(define bespoke
    (gen:let ([kvs gen:kvlist])
        (foldl insert-correct (E) kvs))       
)

(provide bespoke)