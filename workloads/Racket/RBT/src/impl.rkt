#lang racket

(provide (all-defined-out))

(require data/maybe)
(require data/monad)
(require algebraic/control/applicative)

(struct B() #:transparent)

(struct R() #:transparent)

(struct E() #:transparent)

(struct T(color l k v r) #:transparent)

(define (return x) (just x))

(define (apply f x) 
  (match x  
    [(just x) (f x)]
    [(nothing) (nothing)]
  )
)

(define (t c l k v r) (T c l k v r))

(define (blacken t)
  (match t
    [(E) (E)]
    [(T c l k v r) (T (B) l k v r)]
    )
  )

(define (redden t)
  (match t
    [(T B l k v r) (just (T (R) l k v r))]
    [* nothing]
  )
)

(define (balance col tl k v tr)
  (match (list col tl k v tr)
    #|! |#
    [(list (B) (T (R) (T (R) a x vx b) y vy c) z vz d)
        (T (R) T((B) a x vx b) y vy (T (B) c z vz d))
    ]
    #|!! swap_ad|#
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


(define (insert k v t)
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

(define (balLeft tl k v tr)
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
    [* nothing]
  )
)

(define (balRight tl k v tr)
  (match (list tl k v tr)
    [(list a x vx (T (R) b y vy c)) (return (T (R) a x vx (T (B) b y vy c)))]
    [(list (T (B) a x vx b) y vy bl) (return ((balance (B) (T (R) a x vx b) y vy bl)))]
    [(list (T (R)  a x vx (T (B) b y vy c)) z vz bl) 
      #|! |#
      (do [a2  <- (redden a)]
      (return (T (R) (balance (B) a2 x vx b) y vy (T (B) c z vz bl))))

      #|!! miscolor_balRight |#
      #|!
      (return (T (R) (balance (B) a x vx b) y vy (T (B) c z vz bl)))
      |#
    ]
    [* nothing]
  )
)

(define (join t1 t2)
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
            (return (T (R) (T (B) a x vx b2) z vz (T (R) c2 y vy d)))

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
    [(list (T (R) a x vx b) c) (apply (t (R) a x vx) (join b c))]
  )
)

(define (delLeft a y vy b)
  (match a 
    [(T (B) l k v r) (do [a2  <- (del a)] (balLeft a2 y vy b))]
    [* (do [a2  <- (del a)] (return (T (R) a2 y vy b)))]
  )
)

(define (delRight a y vy b)
  (match b 
    [(T (B) l k v r) (do [b2  <- (del b)] (balRight a y vy b2))] 
    [* [T (R) a y vy (apply (t (R) a y vy) (del b))]]
  )        
)

(define (del x t)
  (match t 
    [(E) (return (E))]
    [(T c a y vy b) 
        #|! |#
        (cond
          [(< x y) (delLeft a y vy b)]
          [(> x y) (delRight a y vy b)]
          [else (join a b)]
        )

        #|!! delete_4 |#
        #|! 
        (cond
          [(< x y) (del a)]
          [(> x y) (del b)]
          [else (join a b)]
        )
        |#

        #|!! delete_5 |#
        #|! 
        (cond
          [(> x y) (delLeft a y vy b)]
          [(< x y) (delRight a y vy b)]
          [else (join a b)]
        )
        |#
    ] 
  )
)

(define (delete x tr)
  #|! |#
  (apply blacken (del x tr))

  #|!! miscolor_delete |#
  #|!
    (del x tr)
  |#
)

(define (find x t)
  (match t 
    [(E) (nothing)]
    [(T c l y vy r) (cond [(< x y) (find x l)]
                          [(< y x) (find x r)]
                          [else (just vy)])
    ]
  )
)

(define (size t)
  (match t 
    [(E) 0]
    [(T c l k v r) (1 + (size l) (size r))]
  )
)