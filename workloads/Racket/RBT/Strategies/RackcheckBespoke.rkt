#lang racket

(require "../src/impl.rkt")
(require "../src/spec.rkt")
(require rackcheck)
(require rackunit)
(require data/maybe)
(require algebraic/control/applicative)

(provide (all-defined-out))

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
            [(T rb a y vy b) (cond  [(< x y) (balance-correct rb (insert-aux x vx a) y vy b)]
                                    [(< y x) (balance-correct rb a y vy (insert-aux x vx b))]
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

#| Validity Properties |#

(define test_prop_InsertValid
    (property insertValid ([t bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertValid t k v) (just #t)))
)

(define test_prop_DeleteValid
    (property deleteValid ([t bespoke] [k gen:natural])
        (equal? (prop_DeleteValid t k) (just #t)))
)

#| Post-condition Properties |#

(define test_prop_InsertPost
    (property insertPost ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_InsertPost t k1 k2 v) (just #t)))
)

(define test_prop_DeletePost
    (property deletePost ([t bespoke] [k1 gen:natural] [k2 gen:natural])
        (equal? (prop_DeletePost t k1 k2) (just #t)))
)

#| Model-based Properties |#

(define test_prop_InsertModel
    (property insertModel ([t bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertModel t k v) (just #t)))
)

(define test_prop_DeleteModel
    (property deleteModel ([t bespoke] [k gen:natural])
        (equal? (prop_DeleteModel t k) (just #t)))
)

#| Metamorphic Properties |#

(define test_prop_InsertInsert
    (property insertInsert ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v1 gen:natural] [v2 gen:natural])
        (equal? (prop_InsertInsert t k1 k2 v1 v2) (just #t)))
)

(define test_prop_InsertDelete
    (property insertDelete ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_InsertDelete t k1 k2 v) (just #t)))
)

(define test_prop_DeleteInsert
    (property deleteInsert ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_DeleteInsert t k1 k2 v) (just #t)))
)

(define test_prop_DeleteDelete
    (property deleteDelete ([t bespoke] [k1 gen:natural] [k2 gen:natural])
        (equal? (prop_DeleteDelete t k1 k2) (just #t)))
)
