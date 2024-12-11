#lang racket

(require "../src/Impl.rkt")
(require "../src/Spec.rkt")
(require "../src/Generation.rkt")

(require data/maybe)
(require (only-in rackcheck gen:natural))
(require property-language)

#| Validity Properties |#

(define test_prop_InsertValid
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k v)
                (equal? (prop_InsertValid t k v) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))
               )))


(define test_prop_DeleteValid
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k)
                (equal? (prop_DeleteValid t k) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural)))))


#| Post-condition Properties |#

(define test_prop_InsertPost
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_InsertPost t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))



(define test_prop_DeletePost
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2)
                (equal? (prop_DeletePost t k1 k2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))
               )))

#| Model-based Properties |#

(define test_prop_InsertModel
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k v)
                (equal? (prop_InsertModel t k v) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteModel
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k)
                (equal? (prop_DeleteModel t k) (just #t))
                )
               `((t . ,bespoke) (k . ,gen:natural))
               )))

#| Metamorphic Properties |#

(define test_prop_InsertInsert
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v1 v2)
                (equal? (prop_InsertInsert t k1 k2 v1 v2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v1 . ,gen:natural) (v2 . ,gen:natural))
               )))

(define test_prop_InsertDelete
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_InsertDelete t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteInsert
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2 v)
                (equal? (prop_DeleteInsert t k1 k2 v) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))
               )))

(define test_prop_DeleteDelete
  (lambda (cfg) (run-loop cfg
               (property
                (forall t k1 k2)
                (equal? (prop_DeleteDelete t k1 k2) (just #t))
                )
               `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))
               )))

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