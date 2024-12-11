#lang racket

(provide (all-defined-out))

(require data/maybe)
(require data/monad)
; (require algebraic/control/applicative)

(struct B() #:transparent)

(struct R() #:transparent)

(define color? (lambda (x) (or (B? x) (R? x))))

(struct E() #:transparent)

(struct T(color l k v r) #:transparent)

(define tree? (lambda (x) (or (E? x) (T? x))))

(define (return x)
  (match x
    [(nothing) (nothing)]
    [(just x) (just x)]
    [_ (just x)]
    )
)

(define (apply f x)
  (match x
    [(just x) (f x)]
    [(nothing) (nothing)]
    )
  )

(define/contract (t c l k v r)
  (color? tree? any/c any/c tree? . -> . tree?)
  (T c l k v r))


(define/contract (blacken t)
  (tree? . -> . tree?)
  (match t
    [(E) (E)]
    [(T _ l k v r) (T (B) l k v r)]
    )
  )

(define/contract (redden t)
  (tree? . -> . (maybe/c tree?))
  (match t
    [(T _ l k v r) (just (T (R) l k v r))]
    [_ nothing]
    )
  )

(define/contract (balance col tl k v tr)
  (color? tree? any/c any/c tree? . -> . tree?)
  (match (list col tl k v tr)
    #|! |#
    [(list (B) (T (R) (T (R) a x vx b) y vy c) z vz d)
     (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))
     ]
    #|!! swap_cd|#
    #|!
      [(list (B) (T (R) (T (R) a x vx b) y vy c) z vz d)
             (T (R) (T (B) a x vx b) y vy (T (B) d z vz c))
      ]
    |#
    [(list (B) (T (R) a x vx (T (R) b y vy c)) z vz d)
     (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))
     ]
    #|! |#
    [(list (B) a x vx (T (R) (T (R) b y vy c) z vz d))
     (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))
     ]
    #|!! swap_bc|#
    #|!
      [(list (B) a x vx (T (R) (T (R) b y vy c) z vz d))
             (T (R) (T (B) a x vx c) y vy (T (B) b z vz d))
      ]
    |#
    [(list (B) a x vx (T (R) b y vy (T (R) c z vz d)))
     (T (R) (T (B) a x vx b) y vy (T (B) c z vz d))
     ]
    [(list rb a x vx b) (T rb a x vx b)]
    )
  )


(define/contract (insert k v t)
  (any/c any/c tree? . -> . tree?)
  (define (ins x vx s)
    (match (list x vx s)
      [(list x vx (E))
       #|! |#
       (T (R) (E) x vx (E))
       #|!! miscolor_insert |#
       #|!
        (T (B) (E) x vx (E))
      |#
       ]
      [(list x vx (T rb a y vy b))
       #|! |#
       (cond
         [(< x y) (balance rb (ins x vx a) y vy b)]
         [(< y x) (balance rb a y vy (ins x vx b))]
         [else (T rb a y vx b)]
         )
       #|!! insert_1 |#
       #|!
          (T (R) (E) x vx (E))
        |#

       #|!! insert_2 |#
       #|!
          (if (< x y)
            (balance rb (ins x vx a) y vy b)
            (T rb a y vx b)
          )
        |#

       #|!! insert_3 |#
       #|!
          (cond
            [(< x y) (balance rb (ins x vx a) y vy b)]
            [(< y x) (balance rb a y vy (ins x vx b))]
            [else (T rb a y vy b)]
          )
        |#

       #|!! no_balance_insert_1 |#
       #|!
          (cond
            [(< x y) (T rb (ins x vx a) y vy b)]
            [(< y x) (balance rb a y vy (ins x vx b))]
            [else (T rb a y vx b)]
          )
        |#

       #|!! no_balance_insert_2 |#
       #|!
          (cond
            [(< x y) (balance rb (ins x vx a) y vy b)]
            [(< y x) (T rb a y vy (ins x vx b))]
            [else (T rb a y vx b)]
          )
        |#
       ]
      )
    )
  (blacken (ins k v t))
  )

(define/contract (balLeft tl k v tr)
  (tree? any/c any/c tree? . -> . (maybe/c tree?))
  (match (list tl k v tr)
    [(list (T (R) a x vx b) y vy c) (return (T (R) (T (B) a x vx b) y vy c))]
    [(list bl x vx (T (B) a y vy b)) (return (balance (B) bl x vx (T (R) a y vy b)))]
    [(list bl x vx (T (R) (T (B) a y vy b) z vz c))
     #|! |#
     (do [c2  <- (redden c)]
       (return (T (R) (T (B) bl x vx a) y vy (balance (B) b z vz c2))))

     #|!! miscolor_balLeft |#
     #|!
        (return (T (R) (balance (B) bl x vx b) y vy (balance (B) b z vz c)))
      |#
     ]
    [_ nothing]
    )
  )

(define/contract (balRight tl k v tr)
  (tree? any/c any/c tree? . -> . (maybe/c tree?))
  (match (list tl k v tr)
    [(list a x vx (T (R) b y vy c)) (return (T (R) a x vx (T (B) b y vy c)))]
    [(list (T (B) a x vx b) y vy bl) (return (balance (B) (T (R) a x vx b) y vy bl))]
    [(list (T (R)  a x vx (T (B) b y vy c)) z vz bl)
     #|! |#
     (do [a2  <- (redden a)]
       (return (T (R) (balance (B) a2 x vx b) y vy (T (B) c z vz bl))))

     #|!! miscolor_balRight |#
     #|!
      (return (T (R) (balance (B) a x vx b) y vy (T (B) c z vz bl)))
      |#
     ]
    [_ nothing]
    )
  )

(define/contract (join t1 t2)
  (tree? tree? . -> . (maybe/c tree?))
  (match (list t1 t2)
    [(list (E) a) (return a)]
    [(list a (E)) (return a)]
    [(list (T (R) a x vx b) (T (R) c y vy d))
     (do [t3  <- (join b c)]
       (match t3
         [(T (R) b2 z vz c2)
          #|! |#
          (return (T (R) (T (R) a x vx b2) z vz (T (R) c2 y vy d)))

          #|!! miscolor_join_1 |#
          #|!
            (return (T (R) (T (B) a x vx b2) z vz (T (B) c2 y vy d)))
            |#
          ]
         [bc (return (T (R) a x vx (T (R) bc y vy d)))]
         )
       )
     ]
    [(list (T (B) a x vx b) (T (B) c y vy d))
     (do [t3  <- (join b c)]
       (match t3
         [(T (R) b2 z vz c2)
          #|! |#
          (return (T (R) (T (B) a x vx b2) z vz (T (B) c2 y vy d)))

          #|!! miscolor_join_2 |#
          #|!
            (return (T (R) (T (R) a x vx b2) z vz (T (R) c2 y vy d)))
            |#
          ]
         [bc (balLeft a x vx (T (B) bc y vy d))]
         )
       )
     ]
    [(list a (T (R) b x vx c)) (do [t3  <- (join a b)] (return (T (R) t3 x vx c)))]
    [(list (T (R) a x vx b) c) (do [t3 <- (join b c)] (return (T (R) a x vx t3)))]
    )
  )

(define/contract (delLeft x a y vy b)
  (any/c tree? any/c any/c tree? . -> . (maybe/c tree?))
  (match a
    [(T (B) _ _ _ _) (do [a2  <- (del x a)] (balLeft a2 y vy b))]
    [_ (do [a2  <- (del x a)] (return (T (R) a2 y vy b)))]
    )
  )

(define/contract (delRight x a y vy b)
  (any/c tree? any/c any/c tree? . -> . (maybe/c tree?))
  (match b
    [(T (B) l k v r) (do [b2  <- (del x b)] (balRight a y vy b2))]
    [_ (do [b2  <- (del x b)] (return (T (R) a y vy b2)))]
    )
  )

(define/contract (del x t)
  (any/c tree? . -> . (maybe/c tree?))
  (match t
    [(E) (return (E))]
    [(T c a y vy b)
     #|! |#
     (cond
       [(< x y) (delLeft x a y vy b)]
       [(> x y) (delRight x a y vy b)]
       [else (join a b)]
       )

     #|!! delete_4 |#
     #|!
        (cond
          [(< x y) (del x a)]
          [(> x y) (del x b)]
          [else (join a b)]
        )
        |#

     #|!! delete_5 |#
     #|!
        (cond
          [(> x y) (delLeft x a y vy b)]
          [(< x y) (delRight x a y vy b)]
          [else (join a b)]
        )
        |#
     ]
    )
  )

(define/contract (delete x tr)
  (any/c tree? . -> . (maybe/c tree?))
  #|! |#
  (return (apply blacken (del x tr)))

  #|!! miscolor_delete |#
  #|!
    (del x tr)
  |#
  )

(define/contract (find x t)
  (any/c tree? . -> . (maybe/c any/c))
  (match t
    [(E) (nothing)]
    [(T _ l y vy r) (cond [(< x y) (find x l)]
                          [(< y x) (find x r)]
                          [else (just vy)])
                    ]
    )
  )

(define/contract (size t)
  (tree? . -> . number?)
  (match t
    [(E) 0]
    [(T _ l _ _ r) (+ 1 (size l) (size r))]
    )
  )

