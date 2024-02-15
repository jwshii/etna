#lang racket

(provide (all-defined-out))

(require data/maybe)

(struct E() #:transparent)

(struct T(left k v right) #:transparent)

(define (insert k v t)
  (match t
    [(E) (T (E) k v (E))]
    [(T l key val r)
      #|! |#
      (cond
        [(< k key) (T (insert k v l) key val r)]
        [(> k key) (T l key val (insert k v r))]
        [else (T l key v r)]
      )
    
      #|! insert_1 |#
      #|!
        (T (E) k v (E))
      |#
    
      #|!! insert_2 |#
      #|!
        (if (< k key)
          (T (insert k v l) key val r)
          (T l key v r)
        )
      |#
    
      #|!! insert_3 |#
      #|!
        (cond
          [(< k key) (T (insert k v l) key val r)]
          [(> k key) (T l key val (insert k v r))]
          [else (T l key val r)]
        )
      |#
    ]
  )
)

(define (join l r)
  (match (list l r)
     [(list (E) * ) r]
     [(list * (E)) l]
     [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2))
       (T l1 k1 v1 (T (join r1 l2) k2 v2 r2))
     ]  
  )
)

(define (delete k tree)
  (match tree
    [(E) (E)]
    [(T l key val r)
     #|! |#
     (cond
       [(< k key) (T (delete k l) key val r)]
       [(> k key) (T l key val (delete k r))]
       [else (join l r)]
     )
     #|!! delete_4 |#
     #|!
     (cond
       [(< k key) (delete k l)]
       [(> k key) (delete k r)]
       [else (join l r)]
     )
  
     |#
     
     #|!! delete_5 |#
     #|!
     (cond
      [(< key k) (T (delete k l) key val r)]
      [(> key k) (T l key val (delete k r))]
      [else (join l r)]
     ) 
     |#
   ]
  )
)

(define (below k tree)
  (match (cons k tree)
    [(cons * (E)) (E)]
    [(cons k (T left key val right))
     (if (<= k key)
       (below k left)
       (T left key val (below k right))
     )
    ]
  )
)

(define (above k tree)
  (match (list k tree)
    [(list * (E)) (E)]
    [(list k (T left key val right))
     (if (<= key k)
       (above k right)
       (T (above k left) key val right)
     )
    ]
  )
)


(define (union l r)
  (match (cons l r)
         [(cons (E) *) r]
         [(cons * (E)) l]
         #|! |#
         [(cons (T l k v r) t) (T (union l (below k t)) k v (union r (above k t)))
         ]
         #|!! union_6 |#
         #|!
         [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2)) 
             (T l1 k1 v1 (T (union-helper l2 (- f 1) k2 v2 r2)))
         ]
         |#
         
         #|!! union_7 |#
         #|!
         [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2))
           (cond
             [(= k1 k2) (T (union-helper l1 l2 (- f 1)) k1 v1 (union-helper r1 r2 (- f 1)))]
             [(< k1 k2) (T k1 k1 v1 (T (union-helper r1 l2 (- f 1)) k2 v2 r2))]
             [else ((union-helper (T l2 k2 v2 r2) (T l1 k1 v1 r1) (- f 1)))]
           )
         ]
       
         |#
         #|!! union_8 |#
         #|!
         [(list (T l1 k1 v1 r1) (T l2 k2 v2 r2))
           (cond
             [(= k1 k2) (T (union-helper l1 l2 (- f 1)) k1 v1 (union-helper r1 r2 (- f 1)))]
             [(< k1 k2) (T (union-helper l1 (below k1 l2) (- f 1)) k1 v1
                           (union-helper r1 (T (above k1 l2) k2 v2 r2)) (- f 1))]
             [else ((union-helper (T l2 k2 v2 r2) (T l1 k1 v1 r1) (- f 1)))]
           )
         ]
         |#
    )   
)

(define (find k t)
  (match (list k t)
    [(list * (E)) (nothing)]
    [(list k (T l key val r))
      (cond
        [(< k key) (find k l)]
        [(> k key) (find k r)]
        [else (just val)]
      )
    ]
  )
)

(define (size tree)
  (match tree
    [(E) 0]
    [(T l * * r) (+ 1 (size l) (size r))]
  )
)