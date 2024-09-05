#lang racket

(require "../src/impl.rkt")
(require "../src/spec.rkt")
(require rackcheck)
(require rackcheck/shrink-tree)
(require data/maybe)

(define nat-lst? (list*of positive?))

(require racket/dict)
(require (for-syntax racket/base racket/set syntax/transformer))

;; vars is a list of pairs of keywords to #f or a domain checker/possible generator
(struct property-data (env-param vars pres test-vars test)
  #:sealed
  #:authentic
  #:reflection-name 'property)

(define (check-property/skip-preconds p env)
  (parameterize ([(property-data-env-param p) env])
    ((property-data-test p))))

(define (check-property p env)
  (parameterize ([(property-data-env-param p) env])
    (cond
      [(ormap (λ (pre) (not ((cdr pre)))) (property-data-pres p)) 'discard]
      [((property-data-test p)) 'pass]
      [else 'fail])))

(define-for-syntax (find-vars stx vars)
  (define (top-vars stx)
    (syntax-case stx (#%top)
      [(#%top . x)
       (if (memf (λ (y) (free-identifier=? y #'x)) vars)
           (list (syntax->datum #'x))
           '())]
      [(s . rst) (foldl (λ (stx st) (set-union st (top-vars stx)))
                        (top-vars #'s)
                        (syntax->list #'rst))]
      [_ '()]))
  (top-vars (expand stx)))

(define-for-syntax (parse-property stx)
  #`(let ([env (make-parameter #f)])
      #,(let loop ([stx stx]
                   [vars '()]
                   [pres '()])
          (syntax-case stx (forall implies)
            [((forall x) . rst)
             (when (memf (λ (y) (free-identifier=? #'x y)) vars)
               (raise-syntax-error 'forall "duplicate identifier" #'x))
             #`(let-syntax ([x (make-variable-like-transformer
                                (λ (stx)
                                  #'(dict-ref (env) 'x)))])
                 #,(loop #'rst (cons #'x vars) pres))]
            [((forall x . ys) . rst)
             (loop #'((forall x) (forall . ys) . rst) vars pres)]
            [((implies e) . rst)
             (let ([used (find-vars #'e vars)]
                   [p (car (generate-temporaries #'(impl)))])
               #`(let ([#,p (thunk e)])
                   #,(loop #'rst vars (cons #`(cons '#,used #,p) pres))))]

            [(e)
             #`(property-data env
                              '#,(reverse vars)
                              (list #,@(reverse pres))
                              '#,(find-vars #'e vars)
                              (thunk e))]
            [(e . rst) (raise-syntax-error 'property "undefined property form" #'e)]))))

(define-syntax property
  (lambda (stx)
    (syntax-case stx ()
      [(property e . rst)
       (parse-property #'(e . rst))])))


(define (run-generator g sz) (shrink-tree-val (g (current-pseudo-random-generator) sz)))

(define (run-generators generators n)
  (let ([result (make-hash)]
        [size (inexact->exact (round (log n 2)))])
    (for ([p (in-dict-pairs generators)])
      (dict-set! result (car p) (run-generator (cdr p) size)))
    result))


(struct run-result (time foundbug passed discards counterexample)
  #:transparent)

(define (run-result->json-str rr)
  (format "[|{\"time\": ~a, \"foundbug\": ~a, \"passed\": ~a, \"discards\": ~a, \"counterexample\": \"~a\"}|]"
          (run-result-time rr)
          (if (run-result-foundbug rr) "true" "false")
          (run-result-passed rr)
          (run-result-discards rr)
          (run-result-counterexample rr))
  )

(define (run-loop tests p generators)
  (let ([start (current-inexact-milliseconds)]
        [foundbug #f]
        [passed 0]
        [discards 0]
        [counterexample ""])
    (let loop ([n 1])
      (if (= n tests)
          'passed
          (let ([env (run-generators generators n)])
            (case (check-property p env)
              [(fail) (set! foundbug #t) (set! counterexample (~v env))]
              [(pass) (set! passed (+ 1 passed)) (loop (+ n 1)) ]
              [(discard) (set! discards (+ 1 discards)) (loop (+ n 1))]))))
    (displayln (run-result->json-str (run-result (- (current-inexact-milliseconds) start) foundbug passed discards counterexample)))))

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

; (run-generator gSized 1)


; (run-generator (gen:one-of-total (nothing) (gen:vars (cons (TBool) '()) (TBool))) 1)

; (run-generator (gen:expr (cons (TBool) '()) (TFun (TBool) (TBool)) 2) 3)

(define test_prop_SinglePreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_SinglePreserve e) (just #t))
                           )
                          `((e . ,gSized))
                          )))

(define test_prop_MultiPreserve
  (lambda (cfg) (run-loop cfg
                          (property
                           (forall e)
                           (equal? (prop_MultiPreserve e) (just #t))
                           )
                          `((e . ,gSized))
                          )))


(provide test_prop_SinglePreserve
         test_prop_MultiPreserve)

