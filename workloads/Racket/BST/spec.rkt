#lang racket

(require "./impl.rkt")
(require quickcheck)

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


#| -- Validity Properties. |#

(define (prop_InsertValid t k v)
  (is-BST t)  (is-BST (insert k v t))
)

(define (prop_DeleteValid t k)
   (is-BST t)  (is-BST (delete k t))
)

(define (prop_UnionValid t1 t2)
  ((is-BST t1) (is-BST t2) (is-BST (union t1 t2)))
)

#| ----------- |#

#| -- Postcondition Properties |#





























