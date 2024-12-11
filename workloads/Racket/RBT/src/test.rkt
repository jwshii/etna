#lang racket

(require rackunit)
(require "Impl.rkt")
(require "Spec.rkt")
(require data/maybe)

; isRBT Tests
(check-equal? (isRBT (E)) (just #t))
(check-equal? (isRBT (T (B) (E) 1 1 (E))) (just #t))
(check-equal? (isRBT (insert 2 2 (E))) (just #t))
(check-equal? (isRBT (insert 3 3 (insert 2 2 (E)))) (just #t))
(check-equal? (isRBT (delete 2 (insert 3 3 (insert 2 2 (E))))) (just #t))
(check-equal? (isRBT (delete 3 (insert 3 3 (insert 2 2 (E))))) (just #t))

; Size tests
(check-equal? (size (E)) 0)
(check-equal? (size (T (B) (E) 1 1 (E))) 1)
(check-equal? (size (T (B) (T (B) (E) 1 1 (E)) 2 2 (T (B) (E) 3 3 (E)))) 3)
; Insert tests
(check-equal? (insert 3 3 (insert 2 2 (insert 1 1 (E)))) (T (B) (T (B) (E) 1 1 (E)) 2 2 (T (B) (E) 3 3 (E))))
(check-equal? (insert 2 2 (insert 1 1 (insert 3 3 (E)))) (T (B) (T (B) (E) 1 1 (E)) 2 2 (T (B) (E) 3 3 (E))))
; Find tests
(check-equal? (find 1 (insert 3 3 (insert 2 2 (insert 1 1 (E))))) (just 1))
(check-equal? (find 2 (insert 3 3 (insert 2 2 (insert 1 1 (E))))) (just 2))
(check-equal? (find 3 (insert 3 3 (insert 2 2 (insert 1 1 (E))))) (just 3))
(check-equal? (find 4 (insert 3 3 (insert 2 2 (insert 1 1 (E))))) (nothing))
; Delete tests
(check-equal? 
  (delete 1 (insert 3 3 (insert 2 2 (insert 1 1 (E))))) 
  (T (B) (E) 2 2 (T (R) (E) 3 3 (E))))

