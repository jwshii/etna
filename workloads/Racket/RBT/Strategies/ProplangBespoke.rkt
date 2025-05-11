#lang racket

(require "../src/Impl.rkt")
(require "../src/Spec.rkt")
(require "../src/Generation.rkt")

(require (only-in rackcheck gen:natural))
(require property-language)

#| Validity Properties |#

(define test_prop_InsertValid
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k #:contract real? #:gen gen:natural)
                          (forall v #:gen gen:natural)
                          (equal? (prop_InsertValid t k v) (just #t))))))


(define test_prop_DeleteValid
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k #:contract real? #:gen gen:natural)
                          (equal? (prop_DeleteValid t k) (just #t))))))


#| Post-condition Properties |#

(define test_prop_InsertPost
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (forall v #:gen gen:natural)
                          (equal? (prop_InsertPost t k1 k2 v) (just #t))))))


(define test_prop_DeletePost
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (equal? (prop_DeletePost t k1 k2) (just #t))))))

#| Model-based Properties |#

(define test_prop_InsertModel
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k #:contract real? #:gen gen:natural)
                          (forall v #:gen gen:natural)
                          (equal? (prop_InsertModel t k v) (just #t))))))

(define test_prop_DeleteModel
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k #:contract real? #:gen gen:natural)
                          (equal? (prop_DeleteModel t k) (just #t))))))

#| Metamorphic Properties |#

(define test_prop_InsertInsert
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (forall v1 #:gen gen:natural)
                          (forall v2 #:gen gen:natural)
                          (equal? (prop_InsertInsert t k1 k2 v1 v2) (just #t))))))

(define test_prop_InsertDelete
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (forall v #:gen gen:natural)
                          (equal? (prop_InsertDelete t k1 k2 v) (just #t))))))

(define test_prop_DeleteInsert
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (forall v #:gen gen:natural)
                          (equal? (prop_DeleteInsert t k1 k2 v) (just #t))))))

(define test_prop_DeleteDelete
  (lambda (cfg) (run-loop cfg
                (property (forall t #:contract isRBT #:gen bespoke)
                          (forall k1 #:contract real? #:gen gen:natural)
                          (forall k2 #:contract real? #:gen gen:natural)
                          (equal? (prop_DeleteDelete t k1 k2) (just #t))))))

(provide
 test_prop_InsertValid
 test_prop_DeleteValid
 test_prop_InsertPost
 test_prop_DeletePost
 test_prop_InsertModel
 test_prop_DeleteModel
 test_prop_InsertInsert
 test_prop_InsertDelete
 test_prop_DeleteInsert
 test_prop_DeleteDelete
 )