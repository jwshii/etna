#lang racket

(provide (all-defined-out))

(require "./impl.rkt")
(require rackcheck)
(require data/maybe)

(define (keys t)
  (match t
    [(E) '()]
    [(T l k v r)  (append (keys l) (list k) (keys r))]
  )
)

(define (all f l)
  (match l
    ['() #t]
    [(cons x xs) (and (f x) (all f xs))]
  )
)

(define (is-BST t)
  (match t
    [(E) (just #t)]
    [(T l k v r) (match (cons (is-BST l) (is-BST r))
                   [(cons (just #t) (just #t)) (just (and (all (lambda (k1) (< k1 k)) (keys l))
                                                          (all (lambda (k1) (> k1 k)) (keys r))))]            
                   [* (just #f)]
                 )
                 
    ]
  )
)

(define (to-list t)
  (match t
    [(E) null]
    [(T l k v r) (append (to-list l) (list (list k v)) (to-list r))]
  )
)

(define (assumes p1 p2)
  (match p1
    [(nothing) (nothing)]
    [(just #f) (nothing)]
    [(just #t) p2]
  )
)

#| ----------- |#

#| -- Validity Properties. |#

(define (prop_InsertValid t k v)
  (assumes (is-BST t) (is-BST (insert k v t)))
)

(define (prop_DeleteValid t k)
  (assumes (is-BST t) (is-BST (delete k t)))
)

(define (prop_UnionValid t1 t2)
  (assumes
    (match (list (is-BST t1) (is-BST t2))
             [(list (just #t) (just #t)) (just #t)]
             [* (nothing)]
    )
    (is-BST (union t1 t2)))
)

#| ----------- |#

#| -- Post-condition Properties |#

(define (prop_InsertPost t k1 k2 v)
  (assumes (is-BST t)
           (just (equal? (find k2 (insert k1 v t)) (if (equal? k1 k2) (just v) (find k2 t))))
  )
)

(define (prop_DeletePost t k1 k2)
  (assumes (is-BST t)
           (just (equal? (find k2 (delete k1 t)) (if (= k1 k2) (nothing) (find k2 t))))
  )           
)

(define (prop_UnionPost t1 t2 k)
  (assumes
    (match (cons (is-BST t1) (is-BST t2))
             [(cons (just #t) (just #t)) (just #t)]
             [* (nothing)]
    )
    (just (or (equal? (find k (union t1 t2)) (find k t1)) (equal? (find k (union t1 t2)) (find k t2))))
  )
)

#| ----------- |#

#| -- Model-based Properties |#

(define (deleteKey k l)
   (filter (lambda (kv) (not (= (first kv) k))) l)
)

(define (sorted l)
  (match l
    ['() #t]
    [(cons (cons k v) l2) (match l2
                            [null #t]
                            [(cons (cons k2 v2) l3) (and (< k k2) (sorted l2))]                       
                          )
    ]
  )
)

(define (l_insert k v l)
  (match l
    ['() (list (list k v))]
    [(cons (list k1 v1) xs) (cond
                              [(= k k1) (cons (list k v) xs)]
                              [(< k k1) (cons (list k v) l)]
                              [else (append (list (list k1 v1)) (l_insert k v xs))]
                            )
    ]
  )
)

(define (l_sort l)
  (match l
    ['() null]
    [(cons (list k v) l2) (l_insert k v (l_sort l2))]
  )
)

(define  (l_find k l)
  (match (filter (lambda (kv) (= (first kv) k)) l)
    ['() nothing]
    [(cons kv *) (just (second kv))]
  )
)

(define (l_unionBy f l1 l2)
  (match l1
    ['() l2]
    [(cons (list k v) l1_2)
     (let ([l2_2 (deleteKey k l2)])
       (let ([v1 (match (l_find k l2) [(nothing) v] [(just v1) (f v v1)])])
         (l_insert k v1 (l_unionBy f l1_2 l2_2))))
    ]
  )
)

(define (prop_InsertModel t k v)
  (assumes (is-BST t) (just (equal? (to-list (insert k v t)) (l_insert k v (deleteKey k (to-list t))))))
)

(define (prop_DeleteModel t k)
  (assumes (is-BST t) (just (equal? (to-list (delete k t)) (deleteKey k (to-list t)))))
)

(define (prop_UnionModel t1 t2)
  (assumes (match (cons (is-BST t1) (is-BST t2))
                  [(cons (just #t) (just #t)) (just #t)]
                  [* (nothing)]
           )
           (just (equal? (to-list (union t1 t2))
                         (l_sort (l_unionBy (lambda (x *) x) (to-list t1) (to-list t2)))
                 )
           )
  )
)

#| ----------- |#

(define (treeEq t1 t2)
  (just (equal? (to-list t1) (to-list t2)))
)

#| ----------- |#

#| -- Metamorphic Properties |#

(define (prop_InsertInsert t k1 k2 v1 v2)
  (assumes (is-BST t) (treeEq (insert k1 v1 (insert k2 v2 t))
                              (if (= k1 k2) (insert k1 v1 t) (insert k2 v2 (insert k1 v1 t)))
                      )
          
  )
)

(define (prop_InsertDelete t k1 k2 v)
  (assumes (is-BST t) (treeEq (insert k1 v (delete k2 t))
                              (if (= k1 k2) (insert k1 v t) (delete k2 (insert k1 v t)))
                      )
           
  )
)

(define (prop_InsertUnion t1 t2 k v)
  (assumes (match (cons (is-BST t1) (is-BST t2))
                  [(cons (just #t) (just #t)) (just #t)]
                  [* (nothing)]
           )
           (treeEq (insert k v (union t1 t2)) (union (insert k v t1) t2))
  )
)
 
(define (prop_DeleteInsert t k1 k2 v)
  (assumes (is-BST t) (treeEq (delete k1 (insert k2 v t))
                              (if (= k1 k2) (delete k1 t) (insert k2 v (delete k1 t)))
                      )
  )
)

(define (prop_DeleteDelete t k1 k2)
  (assumes (is-BST t) (treeEq (delete k1 (delete k2 t))
                              (delete k2 (delete k1 t))
                      )
  )          
)

(define (prop_DeleteUnion t1 t2 k)
  (assumes (and (is-BST t1) (is-BST t2))
           (treeEq (delete k (union t1 t2)) (union (delete k t1) (delete k t2)))
  )
)

(define (prop_UnionDeleteInsert t1 t2 k v)
  (assumes (and (is-BST t1) (is-BST t2))
           (treeEq (union (delete k t1) (insert k v t2)) (insert k v (union t1 t2)))
  )
)

(define (prop_UnionUnionIdem t)
  (assumes (is-BST t) (treeEq (union t t) t))          
)

(define (prop_UnionUnionAssoc t1 t2 t3)
  (assumes (and (is-BST t1) (is-BST t2) (is-BST t3))
           (treeEq (union (union t1 t2) t3) (union t1 (union t2 t3)))
  )
)

#| ----------- |#

(define (size-BST t)
  (length (to-list t))
)

#| ----------- |#

#| -- Size Properties |#

