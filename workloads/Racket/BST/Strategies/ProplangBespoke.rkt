#lang racket

(require "../src/Impl.rkt")
(require "../src/Spec.rkt")
(require "../src/Generation.rkt")
(require (only-in rackcheck gen:tuple gen:natural gen:list gen:let))

(require rackcheck/shrink-tree)
(require data/maybe)

(require property-language)

#| Validity Properties |#

(define (test_prop_InsertValid cfg)
  (run-loop cfg
            (property (forall t k v)
                      (implies (BST? t))
                      (implies (real? k))
                      (BST? (insert k v t)))
            `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))))


(define (test_prop_DeleteValid cfg)
  (run-loop cfg
            (property
             (forall t k)
             (implies (BST? t))
             (implies (real? k))
             (BST? (delete k t)))
            `((t . ,bespoke) (k . ,gen:natural))))

(define (test_prop_UnionValid cfg)
  (run-loop cfg
            (property
             (forall t1 t2)
             (implies (BST? t1))
             (implies (BST? t2))
             (BST? (union t1 t2)))
            `((t1 . ,bespoke) (t2 . ,bespoke))))

#| Post-condition Properties |#

(define (test_prop_InsertPost cfg)
  (run-loop cfg
            (property
             (forall t k1 k2 v)
             (implies (BST? t))
             (implies (real? k1))
             (implies (real? k2))
             (equal? (find k2 (insert k1 v t)) (if (= k1 k2) (just v) (find k2 t))))
            `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))))



(define (test_prop_DeletePost cfg)
  (run-loop cfg
            (property
             (forall t k1 k2)
             (implies (BST? t))
             (equal? (find k2 (delete k1 t)) (if (= k1 k2) (nothing) (find k2 t))))
            `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))))


(define (test_prop_UnionPost cfg)
  (run-loop cfg
            (property
             (forall t1 t2 k)
             (implies (BST? t1))
             (implies (BST? t2))
             (implies (real? k))
             (let ([search-union (find k (union t1 t2))]
                   [search-t1 (find k t1)]
                   [search-t2 (find k t2)])
               (if (just? search-t1)
                   (equal? search-union search-t1)
                   (equal? search-union search-t2))))
            `((t1 . ,bespoke) (t2 . ,bespoke) (k . ,gen:natural))))


#| Model-based Properties |#

(define (test_prop_InsertModel cfg)
  (run-loop cfg
            (property
             (forall t k v)
             (implies (BST? t))
             (implies (real? k))
             (equal? (tree->list (insert k v t)) (insert-sorted k v (tree->list t))))
            `((t . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))))

(define (test_prop_DeleteModel cfg)
  (run-loop cfg
            (property
             (forall t k)
             (implies (BST? t))
             (implies (real? k))
             (equal? (tree->list (delete k t)) (remove-key k (tree->list t))))
            `((t . ,bespoke) (k . ,gen:natural))))

(define (test_prop_UnionModel cfg)
  (run-loop cfg
            (property
             (forall t1 t2)
             (implies (BST? t1))
             (implies (BST? t2))
             (equal? (tree->list (union t1 t2))
                     (union-sorted (tree->list t1) (tree->list t2))))
            `((t1 . ,bespoke) (t2 . ,bespoke))))

#| Metamorphic Properties |#

(define (test_prop_InsertInsert cfg)
  (run-loop cfg
            (property
             (forall t k1 k2 v1 v2)
             (implies (BST? t))
             (implies (real? k1))
             (implies (real? k2))
             (tree-equiv? (insert k1 v1 (insert k2 v2 t))
                          (if (= k1 k2)
                              (insert k1 v1 t)
                              (insert k2 v2 (insert k1 v1 t)))))
            `((t . ,bespoke)
              (k1 . ,gen:natural) (k2 . ,gen:natural)
              (v1 . ,gen:natural) (v2 . ,gen:natural))))

(define (test_prop_InsertDelete cfg)
  (run-loop cfg
            (property
             (forall t k1 k2 v)
             (implies (BST? t))
             (implies (real? k1))
             (implies (real? k2))
             (tree-equiv? (insert k1 v (delete k2 t))
                          (if (= k1 k2) (insert k1 v t) (delete k2 (insert k1 v t)))))
            `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))))

(define (test_prop_InsertUnion cfg)
  (run-loop cfg
            (property
             (forall t1 t2 k v)
             (implies (BST? t1))
             (implies (BST? t2))
             (implies (real? k))
             (tree-equiv? (insert k v (union t1 t2))
                          (union (insert k v t1) t2)))
            `((t1 . ,bespoke) (t2 . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))))

(define (test_prop_DeleteInsert cfg)
  (run-loop cfg
            (property
             (forall t k1 k2 v)
             (implies (BST? t))
             (implies (real? k1))
             (implies (real? k2))
             (tree-equiv? (delete k1 (insert k2 v t))
                          (if (= k1 k2) (delete k1 t) (insert k2 v (delete k1 t)))))
            `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural) (v . ,gen:natural))))

(define (test_prop_DeleteDelete cfg)
  (run-loop cfg
            (property
             (forall t k1 k2)
             (tree-equiv? (delete k1 (delete k2 t))
                          (delete k2 (delete k1 t))))
            `((t . ,bespoke) (k1 . ,gen:natural) (k2 . ,gen:natural))))

(define (test_prop_DeleteUnion cfg)
  (run-loop cfg
            (property
             (forall t1 t2 k)
             (implies (BST? t1))
             (implies (BST? t2))
             (implies (real? k))
             (tree-equiv? (delete k (union t1 t2))
                          (union (delete k t1) (delete k t2))))
            `((t1 . ,bespoke) (t2 . ,bespoke) (k . ,gen:natural))))

(define (test_prop_UnionDeleteInsert cfg)
  (run-loop cfg
            (property
             (forall t1 t2 k v)
             (implies (BST? t1))
             (implies (BST? t2))
             (implies (real? k))
             (tree-equiv? (union (delete k t1) (insert k v t2))
                          (insert k v (union t1 t2))))
            `((t1 . ,bespoke) (t2 . ,bespoke) (k . ,gen:natural) (v . ,gen:natural))))

(define (test_prop_UnionUnionIdem cfg)
  (run-loop cfg
            (property
             (forall t)
             (implies (BST? t))
             (tree-equiv? (union t t) t))
            `((t . ,bespoke))))

(define (test_prop_UnionUnionAssoc cfg)
  (run-loop cfg
            (property
             (forall t1 t2 t3)
             (implies (BST? t1))
             (implies (BST? t2))
             (implies (BST? t3))
             (equal? (union (union t1 t2) t3) (union t1 (union t2 t3))))
            `((t1 . ,bespoke) (t2 . ,bespoke) (t3 . ,bespoke))))

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