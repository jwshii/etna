#lang racket

(require "../src/Impl.rkt")
(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require (only-in rackcheck gen:tuple gen:natural gen:list gen:let))

(require rackcheck/shrink-tree)

(require property-language)

#| Validity Properties |#

(define (test_prop_InsertValid cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (BST? (insert k v t))) 8))


(define (test_prop_DeleteValid cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (BST? (delete k t))) 8))

(define (test_prop_UnionValid cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (BST? (union t1 t2))) 8))

#| Post-condition Properties |#

(define (test_prop_InsertPost cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (equal? (find k2 (insert k1 v t)) (if (= k1 k2) (just v) (find k2 t)))) 8))



(define (test_prop_DeletePost cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (equal? (find k2 (delete k1 t)) (if (= k1 k2) (nothing) (find k2 t)))) 8))


(define (test_prop_UnionPost cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (let ([search-union (find k (union t1 t2))]
                            [search-t1 (find k t1)]
                            [search-t2 (find k t2)])
                        (if (just? search-t1)
                            (equal? search-union search-t1)
                            (equal? search-union search-t2)))) 8))


#| Model-based Properties |#

(define (test_prop_InsertModel cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (equal? (tree->list (insert k v t)) (insert-sorted k v (tree->list t)))) 8))

(define (test_prop_DeleteModel cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
             (equal? (tree->list (delete k t)) (remove-key k (tree->list t)))) 8))

(define (test_prop_UnionModel cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (equal? (tree->list (union t1 t2))
                              (union-sorted (tree->list t1) (tree->list t2)))) 8))

#| Metamorphic Properties |#

(define (test_prop_InsertInsert cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (forall v1 #:gen gen:natural)
                      (forall v2 #:gen gen:natural)
                      (tree-equiv? (insert k1 v1 (insert k2 v2 t))
                                   (if (= k1 k2)
                                      (insert k1 v1 t)
                                      (insert k2 v2 (insert k1 v1 t))))) 8))

(define (test_prop_InsertDelete cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (tree-equiv? (insert k1 v (delete k2 t))
                                   (if (= k1 k2) (insert k1 v t) (delete k2 (insert k1 v t))))) 8))

(define (test_prop_InsertUnion cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (tree-equiv? (insert k v (union t1 t2))
                                   (union (insert k v t1) t2))) 8))

(define (test_prop_DeleteInsert cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (tree-equiv? (delete k1 (insert k2 v t))
                                   (if (= k1 k2) (delete k1 t) (insert k2 v (delete k1 t))))) 8))

(define (test_prop_DeleteDelete cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (forall k1 #:contract real? #:gen gen:natural)
                      (forall k2 #:contract real? #:gen gen:natural)
                      (tree-equiv? (delete k1 (delete k2 t))
                                   (delete k2 (delete k1 t)))) 8))

(define (test_prop_DeleteUnion cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (tree-equiv? (delete k (union t1 t2))
                                   (union (delete k t1) (delete k t2)))) 8))

(define (test_prop_UnionDeleteInsert cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (forall k #:contract real? #:gen gen:natural)
                      (forall v #:gen gen:natural)
                      (tree-equiv? (union (delete k t1) (insert k v t2))
                                   (insert k v (union t1 t2)))) 8))

(define (test_prop_UnionUnionIdem cfg)
  (parallel-run-loop cfg
            (property (forall t #:contract BST? #:gen bespoke)
                      (tree-equiv? (union t t) t)) 8))

(define (test_prop_UnionUnionAssoc cfg)
  (parallel-run-loop cfg
            (property (forall t1 #:contract BST? #:gen bespoke)
                      (forall t2 #:contract BST? #:gen bespoke)
                      (forall t3 #:contract BST? #:gen bespoke)
                      (equal? (union (union t1 t2) t3) (union t1 (union t2 t3)))) 8))

; Time, foundbug, #tests, counterexample
(provide
 test_prop_InsertValid
 test_prop_DeleteValid
 test_prop_UnionValid
 test_prop_InsertPost
 test_prop_DeletePost
 test_prop_UnionPost
 test_prop_InsertModel
 test_prop_DeleteModel
 test_prop_UnionModel
 test_prop_InsertInsert
 test_prop_InsertDelete
 test_prop_InsertUnion
 test_prop_DeleteInsert
 test_prop_DeleteDelete
 test_prop_DeleteUnion
 test_prop_UnionDeleteInsert
 test_prop_UnionUnionIdem
 test_prop_UnionUnionAssoc
 )