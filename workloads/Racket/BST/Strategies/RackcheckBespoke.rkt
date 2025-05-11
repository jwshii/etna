#lang racket

(require "../src/Impl.rkt")
(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require rackcheck)
(require rackunit)
(provide (all-defined-out))

#| Validity Properties |#

(define test_prop_InsertValid
    (property insertValid ([t bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertValid t k v) (just #t)))
)

(define test_prop_DeleteValid
    (property deleteValid ([t bespoke] [k gen:natural])
        (equal? (prop_DeleteValid t k) (just #t)))
)

(define test_prop_UnionValid
    (property unionValid ([t1 bespoke] [t2 bespoke])
        (equal? (prop_UnionValid t1 t2) (just #t)))
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

(define test_prop_UnionPost
    (property unionPost ([t1 bespoke] [t2 bespoke] [k gen:natural])
        (equal? (prop_UnionPost t1 t2 k) (just #t)))
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

(define test_prop_UnionModel
    (property unionModel ([t1 bespoke] [t2 bespoke])
        (equal? (prop_UnionModel t1 t2) (just #t)))
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

(define test_prop_InsertUnion
    (property insertUnion ([t1 bespoke] [t2 bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertUnion t1 t2 k v) (just #t)))
)

(define test_prop_DeleteInsert
    (property deleteInsert ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_DeleteInsert t k1 k2 v) (just #t)))
)

(define test_prop_DeleteDelete
    (property deleteDelete ([t bespoke] [k1 gen:natural] [k2 gen:natural])
        (equal? (prop_DeleteDelete t k1 k2) (just #t)))
)

(define test_prop_DeleteUnion
    (property deleteUnion ([t1 bespoke] [t2 bespoke] [k gen:natural])
        (equal? (prop_DeleteUnion t1 t2 k) (just #t)))
)

(define test_prop_UnionDeleteInsert
    (property unionDeleteInsert ([t1 bespoke] [t2 bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_UnionDeleteInsert t1 t2 k v) (just #t)))
)

(define test_prop_UnionUnionIdem
    (property unionUnionIdem ([t bespoke])
        (equal? (prop_UnionUnionIdem t) (just #t)))
)

(define test_prop_UnionUnionAssoc
    (property unionUnionAssoc ([t1 bespoke] [t2 bespoke] [t3 bespoke])
        (equal? (prop_UnionUnionAssoc t1 t2 t3) (just #t)))
)