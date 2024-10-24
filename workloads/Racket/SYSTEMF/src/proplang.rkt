#lang racket

(require racket/dict)
(require (for-syntax racket/base racket/set syntax/transformer))

(provide
 property
 test-condition?
 test-condition-variables

 property-preconditions
 property-check-condition
 
 (rename-out
  [property-data?          property?]
  [property-data-vars      property-variables])
 
 (contract-out
  [check-property (-> property-data? dict? any/c)]
  [check-property/skip-preconditions (-> property-data? dict? any/c)]))

(struct property-data (env-param vars pres test-vars test)
  #:sealed
  #:authentic
  #:reflection-name 'property)

;; property? -> dict? -> (or/c 'pass 'fail)
(define (check-property/skip-preconditions p env)
  (parameterize ([(property-data-env-param p) env])
    (if ((property-data-test p))
        'pass
        'fail)))

;; property? -> dict? -> (or/c 'discard 'fail 'pass)
(define (check-property p env)
  (parameterize ([(property-data-env-param p) env])
    (cond
      [(ormap (λ (pre) (not ((cdr pre)))) (property-data-pres p)) 'discard]
      [((property-data-test p)) 'pass]
      [else 'fail])))

(struct test-condition (env-param variables test)
  #:sealed
  #:authentic
  #:property
  prop:procedure
  (λ (tc env)
    (parameterize ([(test-condition-env-param tc) env])
      ((test-condition-test tc)))))

;; property? -> (listof test-condition?)
(define (property-preconditions p)
  (map (λ (pp) (test-condition (property-data-env-param p) (car pp) (cdr pp)))
       (property-data-pres p)))

;; property? -> test-condition?
(define (property-check-condition p)
  (test-condition (property-data-env-param p)
                  (property-data-test-vars p)
                  (property-data-test p)))


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