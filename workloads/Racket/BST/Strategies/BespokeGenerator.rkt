#lang racket

(require "../impl.rkt")
(require "../spec.rkt")
(require rackcheck)
(require rackunit)
(require data/maybe)
(require racket/trace) 

(define (insert_correct kv t)
  (let ([k (first kv)])
     (let([v (second kv)])
         (match t
           [(E) (T (E) k v (E))]
           [(T l k2 v2 r) (cond
                            [(< k k2) (T (insert_correct kv l) k2 v2 r)]
                            [(> k k2) (T l k2 v2 (insert_correct kv r))]
                            [else (T l k2 v r)]
                          )
           ]
         )
     )
  )
)

(define config (make-config #:tests 1000))

(define gen:kv (gen:tuple gen:natural gen:natural))

(define gen:kvlist (gen:list gen:kv))

(define bespoke
     (gen:let ([kvs gen:kvlist])
        (foldl insert_correct (E) kvs)
     )       
)

#| Validity Properties |#

(check-property config
    (property insertValid ([t bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertValid t k v) (just #t)))
)


(check-property config
    (property deleteValid ([t bespoke] [k gen:natural])
        (equal? (prop_DeleteValid t k) (just #t)))
)

(check-property config
    (property unionValid ([t1 bespoke] [t2 bespoke])
        (equal? (prop_UnionValid t1 t2) (just #t)))
)

#| Post-condition Properties |#

(check-property config
    (property insertPost ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_InsertPost t k1 k2 v) (just #t)))
)

(check-property config
    (property deletePost ([t bespoke] [k1 gen:natural] [k2 gen:natural])
        (equal? (prop_DeletePost t k1 k2) (just #t)))
)

(check-property config
    (property unionPost ([t1 bespoke] [t2 bespoke] [k gen:natural])
        (equal? (prop_UnionPost t1 t2 k) (just #t)))
)

#| Model-based Properties |#

(check-property config
    (property insertModel ([t bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertModel t k v) (just #t)))
)

(check-property config
    (property deleteModel ([t bespoke] [k gen:natural])
        (equal? (prop_DeleteModel t k) (just #t)))
)

(check-property config
    (property unionModel ([t1 bespoke] [t2 bespoke])
        (equal? (prop_UnionModel t1 t2) (just #t)))
)

#| Metamorphic Properties |#

(check-property config
    (property insertInsert ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v1 gen:natural] [v2 gen:natural])
        (equal? (prop_InsertInsert t k1 k2 v1 v2) (just #t)))
)

(check-property config
    (property insertDelete ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_InsertDelete t k1 k2 v) (just #t)))
)

(check-property config
    (property insertUnion ([t1 bespoke] [t2 bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_InsertUnion t1 t2 k v) (just #t)))
)

(check-property config
    (property deleteInsert ([t bespoke] [k1 gen:natural] [k2 gen:natural] [v gen:natural])
        (equal? (prop_DeleteInsert t k1 k2 v) (just #t)))
)

(check-property config
    (property deleteDelete ([t bespoke] [k1 gen:natural] [k2 gen:natural])
        (equal? (prop_DeleteDelete t k1 k2) (just #t)))
)

(check-property config
    (property deleteUnion ([t1 bespoke] [t2 bespoke] [k gen:natural])
        (equal? (prop_DeleteUnion t1 t2 k) (just #t)))
)

(check-property config
    (property unionDeleteInsert ([t1 bespoke] [t2 bespoke] [k gen:natural] [v gen:natural])
        (equal? (prop_UnionDeleteInsert t1 t2 k v) (just #t)))
)

(check-property config
    (property unionUnionIdem ([t bespoke])
        (equal? (prop_UnionUnionIdem t) (just #t)))
)

(check-property config
    (property unionUnionAssoc ([t1 bespoke] [t2 bespoke] [t3 bespoke])
        (equal? (prop_UnionUnionAssoc t1 t2 t3) (just #t)))
)