#lang racket

(require "Impl.rkt")
(require "Spec.rkt")
(require rackcheck)
(require data/maybe)

(define nat-lst? (list*of positive?))

(define (gen:bind-opt g f)
  (gen:bind g
            (lambda (maybe-x)
              (match maybe-x
                [(nothing) (gen:const nothing)]
                [(just x) (f x)]
                )
              ))
  )


(define/contract (list-pop ls index)
  (-> (listof any/c) exact-integer? (values any/c (listof any/c)))
  (let ([index (+ index 1)])
    (if (> index (length ls))
        (values (raise-argument-error) ls)
        (match/values (split-at ls index)
                      [(l1 l2) (values (last l1) (append (take l1 (- (length l1) 1)) l2))]
                      )
        )
    ))



(define (backtrack gs)
  (define (backtrack-iter gs)
    (if (null? gs)
        (gen:const nothing)
        ; Pull a random generator from the list
        (let [(index (random 0 (length gs)))]
          (let-values ([(g gs2) (list-pop gs index)])
            (gen:bind g
                      (lambda (x)
                        (match x
                          [(nothing) (backtrack-iter gs2)]
                          [(just x) (gen:const (just x))]
                          )
                        )
                      )
            )
          )
        ))
  (backtrack-iter gs)
  )


(define (gen:var ctx t p r)
  (match ctx
    ['() r]
    [(cons t2 ctx2) (if (equal? t t2)
                        (gen:var ctx2 t (+ p 1) (cons p r))
                        (gen:var ctx2 t (+ p 1) r))]
    )
  )


(define (gen:vars ctx t)
  (let [(var-nats (gen:var ctx t 0 '()))]
    (map (lambda (p) (gen:const (just (Var p)))) var-nats)
    )
  )


(define (gen:zero env tau)
  (match tau
    [(TBool) (gen:bind gen:boolean (lambda (b) (gen:const (just (Bool b)))))]
    [(TFun T1 T2) (gen:bind-opt (gen:zero (cons T1 env) T2)
                                (lambda (e) (gen:const (just (Abs T1 e)))))]
    )
  )

(define gen:typ
  (gen:frequency
   `(
     (2 . ,(gen:const (TBool)))
     (1 . ,(gen:bind (gen:delay gen:typ)
                     (lambda (T1) (gen:bind (gen:delay gen:typ)
                                            (lambda (T2) (gen:const (TFun T1 T2)))))
                     )
        )
     )
   ))

(define/contract (gen:one-of-total fallback gs)
  (-> any/c (listof gen?) gen?)
  (if (null? gs)
      (gen:const fallback)
      (apply gen:choice gs)
      )
  )

(define/contract (gen:expr env tau sz)
  (-> (listof typ?) typ? number? gen?)
  (match sz
    [0 (backtrack (list
                   (gen:one-of-total nothing (gen:vars env tau))
                   (gen:zero env tau)))]
    [n (backtrack (list
                   (gen:one-of-total nothing (gen:vars env tau))
                   (gen:bind gen:typ
                             (lambda (T1) (gen:bind-opt (gen:expr env (TFun T1 tau) (- n 1))
                                                        (lambda (e1) (gen:bind-opt (gen:expr env T1 (- n 1))
                                                                                   (lambda (e2) (gen:const (just (App e1 e2)))))))))
                   (match tau
                     [(TBool) (gen:bind gen:boolean (lambda (b) (gen:const (just (Bool b)))))]
                     [(TFun T1 T2) (gen:bind-opt (gen:expr (cons T1 env) T2 (- n 1))
                                                 (lambda (e) (gen:const (just (Abs T1 e)))))]
                     )))]
    )
  )


(define gSized
  (gen:bind gen:typ
            (lambda (tau)
              (gen:bind-opt (gen:expr '() tau 10) (lambda (x) (gen:const x))))))

(provide gSized)