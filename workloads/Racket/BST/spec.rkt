#lang racket

(require "./impl.rkt")

(define (keys t)
  (match t
    [(E) '()]
    [(T l k v r) (list k (keys l) (keys r))]
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
    [(E) #t]
    [(T l k v r) (and (is-BST l) (is-BST r)
                 (all (lambda (k1) (< k1 k)) (keys l))
                 (all (lambda (k1) (> k1 k)) (keys r)))
    ]
  )
)

(define (to-list t)
  (match t
    [(E) '()]
    [(T l k v r) (list (to-list l) (cons k v) (to-list r))]
  )
)

(define (assumes p1 p2)
  (match p1
    [(None) (None)]
    [(Some v)
        (if (= v #f)
            (None)
            (p2)
        )
    ]
  )
)

#| -- Validity Properties. |#

(define (prop_InsertValid t k v)
  (assumes (is-BST t)  (is-BST (insert k v t)))
)

(define (prop_DeleteValid t k)
  (assumes (is-BST t)  (is-BST (delete k t)))
)

(define (prop_UnionValid t1 t2)
  (assumes (and (is-BST t1) (is-BST t2)) (is-BST (union t1 t2)))
)

#| ----------- |#

#| -- Post-condition Properties |#

(define (prop_Insertpost t k1 k2 v)
  (assumes (is-BST t)
           ( = (find k2 (insert k1 v t)) (if (= k1 k2) (Some v) (find k2 t)))
  )
)

(define (prop_Deletepost t k1 k2)
  (assumes (is-BST t)
           (= (find k2 (delete k1 t)) (if (= k1 k2) (None) (find k2 t)))
  )           
)

(define (prop_UnionPost t1 t2 k)
  (or (= (find k (union t1 t2)) (find k t1)) (= (find k (union t1 t2)) (find k t2)))                   
)

#| ----------- |#

#| -- Model-based Properties |#

(define (deleteKey k l)
   (filter (lambda (pair) (not (= (car pair) k))) l)
)

(define (sorted l)
  (match l
    ['() #t]
    [(cons (cons k v) l2) (match l2
                            ['() #t]
                            [(cons (cons k2 v2) l3) (and (< k k2) (sorted l2))]                       
                          )
    ]
  )
)

(define (l_insert k v l)
  (match l
    ['() (cons k v)]
    [(cons (cons k1 v1) xs) (cond
                              [(= k k1) (cons (cons k v) xs)]
                              [(< k k1) (cons (cons k v) l)]
                              [else (cons (cons k1 v1) (l_insert k v xs))]
                            )
    ]
  )
)

(define (prop_InsertModel t k v)
  (assumes (is-BST t) (= (insert k v t) (l_insert (cons k v) (deleteKey k (to-list t)))))
)

(define (prop_DeleteModel t k)
  (assumes (is-BST t) (= (to-list (delete k t ))) (deleteKey k (to-list t)))
)

(define (l_sort l)
  (match l
    ['() ('())]
    [(cons (cons k v) l2) (l_insert (cons k v) (l_sort l2))]
  )
)

(define  (l_find k l)
  (match (filter (lambda (x *) = x k) l)
    ['() (None)]
    [(cons (cons * v) *) (Some v)]
  )
)

(define (l_unionBy f l1 l2)
  (match l1
    ['() l2]
    [(cons (cons k v) l1_2)
     (let ([l2_2 (deleteKey k l2)])
       (let ([v1 (match (l_find k l2)
                    [(None) v]
                    [(Some v1) (f v v1)])])
         (l_insert (cons k v1) (l_unionBy f l1_2 l2_2))))
    ]
  )
)


(define (prop_UnionModel t1 t2)
  (assumes (and (is-BST t1) (is-BST t2))
           (= (to-list (union t1 t2))
              (l_sort (l_unionBy (lambda (x *) x) (to-list t1) (to-list t2)))
           )
  )
)

#| ----------- |#

(define (treeEq t1 t2)
  (match (list t1 t2)
    [(list (E) (E)) #t]
    [(list (E) *) #f]
    [(list * (E)) #f]
    [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2))
           (and (= k1 k2) (= v1 v2) (treeEq l1 l2) (treeEq r1 r2))
    ]
  )
)

#| ----------- |#

#| -- Metamorphic Properties |#

(define (prop_InsertInsert t k1 k2 v1 v2)
  (assumes (is-BST t) (treeEq (insert k1 v1 (delete k2 t))
                              (if (= k1 k2) (insert k1 v1 t) (insert k2 v2 (insert k1 v1 t)))
                      )
          
  )
)

(define (prop_InsertDelete t k1 k2 v)
  (assumes (is-BST t) (treeEq (insert k1 v (delete k2 t)))
                              (if (= k1 k2) (insert k1 v t) (delete k2 (insert k1 v t)))
           
  )
)

(define (prop_InsertUnion t1 t2 k v)
  (assumes (and (is-BST t1) (is-BST t2))
           (treeEq (union t1 t2) (union (insert k v t1) t2))
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
