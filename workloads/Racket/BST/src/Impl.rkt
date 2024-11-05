#lang racket

(provide (all-defined-out))

(require data/maybe)

(struct E () #:transparent)
(struct T (left k v right) #:transparent)

(define (insert k v t)
  (match t
    [(E) (T (E) k v (E))]
    [(T l k2 v2 r)
     #|! |#
     (cond
       [(< k k2) (T (insert k v l) k2 v2 r)]
       [(> k k2) (T l k2 v2 (insert k v r))]
       [else (T l k2 v r)])

     #|!! insert_1 |#
     #|!
       (T (E) k v (E))
      |#

     #|!! insert_2 |#
     #|!
        (if (< k k2)
          (T (insert k v l) k2 v2 r)
          (T l k2 v r))
      |#

     #|!! insert_3 |#
     #|!
        (cond
          [(< k k2) (T (insert k v l) k2 v2 r)]
          [(> k k2) (T l k2 v2 (insert k v r))]
          [else (T l k2 v2 r)])
      |#
     ]))

(define (join l r)
  (match (list l r)
    [(list (E) _) r]
    [(list _ (E)) l]
    [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2))
     (T l1 k1 v1 (T (join r1 l2) k2 v2 r2))]))

(define (delete k t)
  (match t
    [(E) (E)]
    [(T l key val r)
     #|! |#
     (cond
       [(< k key) (T (delete k l) key val r)]
       [(> k key) (T l key val (delete k r))]
       [else (join l r)])
     #|!! delete_4 |#
     #|!
     (cond
       [(< k key) (delete k l)]
       [(> k key) (delete k r)]
       [else (join l r)])
     |#
     #|!! delete_5 |#
     #|!
     (cond
      [(< key k) (T (delete k l) key val r)]
      [(> key k) (T l key val (delete k r))]
      [else (join l r)])
     |#
     ]))

(define (below k tree)
  (match (cons k tree)
    [(cons _ (E)) (E)]
    [(cons k (T left key val right))
     (if (<= k key)
         (below k left)
         (T left key val (below k right)))]))

(define (above k tree)
  (match (list k tree)
    [(list _ (E)) (E)]
    [(list k (T left key val right))
     (if (<= key k)
         (above k right)
         (T (above k left) key val right))]))


(define (union l r)
  (match (cons l r)
    [(cons (E) _) r]
    [(cons _ (E)) l]
    #|! |#
    [(cons (T l k v r) t) (T (union l (below k t)) k v (union r (above k t)))]

    #|!! union_6 |#
    #|!
         [(cons (T l1 k1 v1 r1) (T l2 k2 v2 r2)) (T l1 k1 v1 (T (union r1 l2) k2 v2 r2))]
         |#

    #|!! union_7 |#
    #|!
         [(cons (T l1 k1 v1 r1) (T l2 k2 v2 r2))
           (cond
             [(= k1 k2) (T (union l1 l2) k1 v1 (union r1 r2))]
             [(< k1 k2) (T l1 k1 v1 (T (union r1 l2 ) k2 v2 r2))]
             [else (union (T l2 k2 v2 r2) (T l1 k1 v1 r1))]
           )
         ]
         |#

    #|!! union_8 |#
    #|!
         [(cons (T l1 k1 v1 r1) (T l2 k2 v2 r2))
           (cond
             [(= k1 k2) (T (union l1 l2) k1 v1 (union r1 r2))]
             [(< k1 k2) (T (union l1 (below k1 l2)) k1 v1 (union r1 (T (above k1 l2) k2 v2 r2)))]
             [else (union (T l2 k2 v2 r2) (T l1 k1 v1 r1))]
           )
         ]
         |#
    )
  )

(define (find k t)
  (match (list k t)
    [(list _ (E)) (nothing)]
    [(list k (T l k2 v2 r))
     (cond
       [(< k k2) (find k l)]
       [(> k k2) (find k r)]
       [else (just v2)])]))

(define (size tree)
  (match tree
    [(E) 0]
    [(T l _ _ r) (+ 1 (size l) (size r))]))