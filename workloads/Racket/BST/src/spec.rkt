#lang racket

(provide (all-defined-out))

(require "./impl.rkt")
(require data/maybe)

;; tree A -> listof real
(define (keys t)
  (match t
    [(E) '()]
    [(T l k v r) (append (keys l) (list k) (keys r))]))

;; tree A -> bool
(define (BST? t)
  (match t
    [(E) #t]
    [(T l k v r)
     (if (and (BST? l) (BST? r))
         (and (andmap (lambda (k1) (< k1 k)) (keys l))
              (andmap (lambda (k1) (> k1 k)) (keys r)))
         #f)]))

;; tree A -> listof A
(define (tree->list t)
  (match t
    [(E) null]
    [(T l k v r) (append (tree->list l) (list (cons k v)) (tree->list r))]))

;; (or bool 'nothing) -> (or bool 'nothing)
(define (assumes p1 p2)
  (match p1
    [(nothing) nothing]
    [#f nothing]
    [#t p2]))

#| ----------- |#

#| -- Model-based Properties |#

(define (remove-key k l)
  (filter (lambda (kv) (not (= (car kv) k))) l))

(define (sorted? l)
  (match l
    ['() #t]
    [(cons (cons k v) l2)
     (match l2
       ['() #t]
       [(cons (cons k2 v2) l3)
        (and (< k k2) (sorted? l2))])]))

(define (insert-sorted k v l)
  (match l
    ['() (list (cons k v))]
    [(cons (cons k1 v1) rst)
     (cond
       [(= k k1) (cons (cons k v) rst)]
       [(< k k1) (cons (cons k v) l)]
       [else (cons (cons k1 v1) (insert-sorted k v rst))])]))

(define (union-sorted l1 l2)
  (match l1
    ['() l2]
    [(cons (cons k v) rst1)
     (union-sorted rst1 (insert-sorted k v l2))]))

#| ----------- |#

(define (tree-equiv? t1 t2)
  (just (equal? (tree->list t1) (tree->list t2))))

#| ----------- |#

#| -- Metamorphic Properties |#

#| ----------- |#

(define (size-BST t)
  (length (tree->list t)))

#| ----------- |#

#| -- Size Properties |#

