#lang racket

(provide (all-defined-out))

(require "./impl.rkt")
(require rackcheck)
(require data/maybe)
(require data/functor)

(define (is-BST-Helper p t)
  (match t 
    [(E) #t]
    [(T c a x v b) (and (p x) (is-BST-Helper p a ) (is-BST-Helper p b))]
  )
)

(define (is-BST t)
  (match t 
    [(E) #t]
    [(T c a x v b) (and (is-BST a) (is-BST b) 
                        (is-BST-Helper (lambda (x y) (< x y)) b)
                        (is-BST-Helper (lambda (x y) (> x y)) b)
                   )
    ]
  )
)

(define (blackRoot t)
  (match t 
    [(T (R) l k v r) #f]
    [* #t]
  )
)

(define (noRedRed t)
  (match t 
    [(E) #t]
    [(T (B) a k v b) (and (noRedRed a) (noRedRed b))]
    [(T (R) a k v b) (and (blackRoot a) (blackRoot b) (noRedRed a) (noRedRed b))]
  )
)

(define (isBlack rb)
  (match rb 
    [(B) 1]
    [(R) 0]
  )
)

(define (go t)
  (match t 
    [(E) (cons #t 1)]
    [(T rb a k v b) 
        ((let ([aRes (go a)])
          (let ([bRes (go b)])
            (let ([aBool (car aRes)])
              (let ([bBool (car bRes)])
                (let ([aHeight (cdr aRes)])
                  (let ([bHeight (cdr bRes)])
                    (cons (and car aRes car bRes (= aHeight bHeight)) (+ aHeight (isBlack rb))))))))))
    ]
  )
)

(define (consistentBlackHeight t)
  (car (go t))
)

(define (isRBT t)
  (just (and (is-BST t) (consistentBlackHeight t) (noRedRed t)))
)

(define (to-list t)
  (match t 
    [(E) '()]
    [(T c l k v r) (append (to-list l) (list (list k v)) (to-list r))]
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
  (assumes (isRBT t) (isRBT (insert k v t)))
)

(define (prop_DeleteValid t k)
  (assumes (isRBT t) (isRBT (delete k t)))
)

#| ----------- |#

#| -- Postcondition Properties. |#


(define (prop_InsertPost t k1 k2 v)
  (assumes (isRBT t)
           (just (equal? (map (find k2) (insert k1 v t)) (if (= k1 k2) (nothing) (find k2 t))))
  )
)

(define (prop_DeletePost t k1 k2)
  (assumes (isRBT t)
           (just (equal? (map (find k2) (delete k1 t))  (if (= k1 k2) (nothing) (find k2 t))))
  )           
)

#| ----------- |#

#| -- Model-based Properties. |#

(define (delete-key k l)
  (filter (lambda (kv) (not (= (first kv) k))) l) 
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

(define (prop_InsertModel t k v)
  (assumes (isRBT t)
           (just (equal? (map to-list (insert k v t) (l_insert k v (delete-key k (to-list t))))))
  )           
)

(define (prop_DeleteModel t k)
  (assumes (isRBT t)
           (just (equal? (map to-list (delete k t)) (delete-key k (to-list t))))
  )           
)

#| ----------- |#

#| -- Metamorphic Properties. |#

(define (compare-op-list t1 t2)
  (match (list t1 t2)
    [(list (just t1) (just t2)) (equal? (to-list t1) (to-list t2))]
    [* #f]
  )
)

(define (prop_InsertInsert t k1 k2 v1 v2)
  (assumes (isRBT t)
           (just (equal? (to-list (insert k1 v1 (insert k2 v2 t))) 
                         (to-list (if (= k1 k2) (insert k1 v1 t) (insert k2 v2 (insert k1 v1 t))))))
  )           
)

(define (prop_InsertDelete t k1 k2 v)
  (assumes (isRBT t)
           (just (equal? (to-list (insert k1 v (delete k2 t))) 
                         (to-list (if (= k1 k2) (insert k1 v t) (delete k2 (insert k1 v t))))))
  )           
)

(define (prop_DeleteInsert t k1 k2 v)
  (assumes (isRBT t)
           (just (equal? (to-list (delete k1 (insert k2 v t))) 
                         (to-list (if (= k1 k2) (delete k1 t) (insert k1 v (delete k1 t))))))
  )           
)

(define (prop_DeleteDelete t k1 k2)
  (assumes (isRBT t)
           (just (equal? (to-list (delete k1 (delete k2 t))) 
                         (to-list (delete k2 (delete k1 t)))))
  )           
)

#| ----------- |#

(define (size-RBT t)
  (length (to-list t))
)