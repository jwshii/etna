#lang racket

(require "./impl.rkt")
(require rackcheck)
(require data/maybe)

(define (assumes p1 p2)
  (match p1
    [(nothing) nothing]
    [(just #f) nothing]
    [(just #t) p2]
    [#t p2]
  )
)