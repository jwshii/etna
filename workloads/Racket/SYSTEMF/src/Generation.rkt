#lang racket

(require (only-in "Impl.rkt" term? typ? Top TVar Arr All Var Abs App TAbs TApp pstep/correct))
(require "Util.rkt")
(require "Type.rkt")
(require rackcheck)
(require data/maybe)

(define/contract (list-pop ls index)
  (-> (listof any/c) exact-integer? (values any/c (listof any/c)))
  (let ([index (+ index 1)])
    (if (> index (length ls))
        (values (raise-argument-error) ls)
        (match/values (split-at ls index)
                      [(l1 l2) (values (last l1) (append (take l1 (- (length l1) 1)) l2))]))))

(define (backtrack gs)
  (define (backtrack-iter gs)
    (if (null? gs)
        (gen:const (nothing))
        ; Pull a random generator from the list
        (let [(index (random 0 (length gs)))]
          (let-values ([(g gs2) (list-pop gs index)])
            (gen:bind g
                      (lambda (x)
                        (match x
                          [(nothing) (backtrack-iter gs2)]
                          [(just x) (gen:const (just x))])))))))
  (backtrack-iter gs))

(define/contract (count-tvar e)
  (env? . -> . exact-integer?)
  (match e
    [(Empty) 0]
    [(EVar e _) (count-tvar e)]
    [(EBound e _) (+ 1 (count-tvar e))]))

(define/contract (exact-tvar0 e)
  (env? . -> . (maybe/c gen?))
  (match (count-tvar e)
    [0 (nothing)]
    [n (just (
      gen:bind (gen:integer-in 0 (- n 1))
               (lambda (i) (gen:const (TVar i)))))]))


(define/contract (gen:exact-typ0 e)
  (env? . -> . gen?)
  (match (exact-tvar0 e)
      [(nothing) (gen:const (All (Top) (Arr (TVar 0) (TVar 0))))]
      [(just g) (gen:bind g (lambda (ty) (gen:const (Arr ty ty))))]))


(define/contract (gen:exact-typ n e)
  (exact-integer? env? . -> . gen?)
  (if (zero? n)
      (gen:exact-typ0 e)
      (gen:frequency
       (list
        ;  genAll
        (cons 2 (gen:bind
                 (gen:choice (gen:const (Top)) (gen:exact-typ (- n 1) e)) 
                 (lambda (ty1) (gen:bind (gen:exact-typ (- n 1) (EBound e ty1)) 
                 (lambda (ty2) (gen:const (All ty1 ty2)))))))
        ;  genArr
        (cons 2 (gen:bind
                (match (exact-tvar0 e)
                  [(nothing) (gen:exact-typ (- n 1) e)]
                  [(just g) (gen:choice (gen:exact-typ (- n 1) e) g)])
                (lambda (ty1) (gen:bind (gen:exact-typ (- n 1) (EVar e ty1))
                (lambda (ty2) (gen:const (Arr ty1 ty2)))))))
        (cons 1 (gen:exact-typ0 e))))))



(define/contract (tshift-correct x typ)
  (number? typ? . -> . typ?)
  (match typ
    [(Top) (Top)]
    [(TVar y) (if (<= x y) (TVar (+ 1 y)) (TVar y))]
    [(Arr ty1 ty2) (Arr (tshift-correct x ty1) (tshift-correct x ty2))]
    [(All ty1 ty2) (All (tshift-correct x ty1) (tshift-correct (+ 1 x) ty2))]))

(define/contract (tlift n ty)
  (exact-integer? typ? . -> . typ?)
  (if (zero? n)
      ty
      (tlift (- n 1) (tshift-correct 0 ty))))

(define/contract (gen:bound-vars e ty)
  (env? typ? . -> . gen?)
  (letrec (
    [go (lambda (n m e ty)
        (match e
          [(Empty) '()]
          [(EBound e _) (go n (+ 1 m) e ty)]
          [(EVar e ty1) (
            let ([rest (go (+ 1 n) m e ty)])
              (if (equal? ty (tlift m ty1))
                  (cons (Var n) rest)
                  rest))]))]
    [vars (go 0 0 e ty)])
    (match vars
      ['() (gen:const nothing)]
      [vars (gen:one-of (map (lambda (v) (just v)) vars))])))


(define/contract (gen:exact-term0 e ty)
  (env? typ? . -> . gen?)
  (let (
    [g (match ty
        [(Arr ty1 ty2) (gen:bind (gen:exact-term0 (EVar e ty1) ty2)
                        (lambda (g) (match g
                          [(nothing) (gen:const nothing)]
                          [(just g) (gen:const (just (Abs ty1 g)))])))]
        [(All ty1 ty2) (gen:bind (gen:exact-term0 (EBound e ty1) ty2)
                        (lambda (g) (match g
                          [(nothing) (gen:const nothing)]
                          [(just g) (gen:const (just (TAbs ty1 g)))])))]
        [_ (gen:const nothing)])])
  (backtrack (list g (gen:bound-vars e ty)))))


(define/contract (fetch-candidate-typs typ)
  (typ? . -> . (listof typ?))
  (letrec (
    [fetchp (lambda (n ty) (match ty
      [(Top) #t]
      [(TVar n-prime) (<= n n-prime)]
      [(Arr ty1 ty2) (and (fetchp n ty1) (fetchp n ty2))]
      [(All ty1 ty2) (and (fetchp n ty1) (fetchp (+ 1 n) ty2))]))]
    [tunshift (lambda (n ty) (match ty
      [(Top) (Top)]
      [(TVar n-prime) (TVar (- n-prime n))]
      [(Arr ty1 ty2) (Arr (tunshift n ty1) (tunshift n ty2))]
      [(All ty1 ty2) (All (tunshift n ty1) (tunshift (+ 1 n) ty2))]))]
    [f (lambda (n ty) (let (
      [l1 (if (fetchp n ty) (list (tunshift n ty)) '())]
      [l2 (match ty
            [(Arr ty1 ty2) (append (f n ty1) (f n ty2))]
            [(All ty1 ty2) (append (f n ty1) (f (+ 1 n) ty2))]
            [_ '()])])
      (append l1 l2)))])
    (f 0 typ)))


(define/contract (gen:cand typ)
  (typ? . -> . gen?)
  (let ([cands (fetch-candidate-typs typ)])
    (if (null? cands)
        (gen:const nothing)
        (gen:one-of (map just cands)))))


(define/contract (gen:replace-typ n ty ty-prime)
  (exact-integer? typ? typ? . -> . gen?)
  (letrec (
    [g1 (if (equal? ty ty-prime) (cons (+ n 2) (gen:const (TVar n))) (cons 1 (gen:const ty)))]
    [g2 (cons (+ 2 n) (match ty
          [(Arr ty1 ty2) (gen:bind (gen:replace-typ n ty1 ty-prime)
                          (lambda (ty1-prime) (gen:bind (gen:replace-typ n ty2 ty-prime)
                          (lambda (ty2-prime) (gen:const (Arr ty1-prime ty2-prime))))))]
          [(All ty1 ty2) (gen:bind (gen:replace-typ n ty1 ty-prime)
                          (lambda (ty1-prime) (gen:bind (gen:replace-typ (+ 1 n) ty2 (tshift-correct 0 ty-prime))
                          (lambda (ty2-prime) (gen:const (All ty1-prime ty2-prime))))))]
          [_ (gen:frequency (list g1))]))])
    (gen:frequency (list g1 g2))))


(define/contract (gen:replace ty)
  (typ? . -> . gen?)
  (gen:bind (gen:cand ty)
  (lambda (mty1) (match mty1
    [(nothing) (gen:const nothing)]
    [(just ty1) (gen:bind (gen:replace-typ 0 (tshift-correct 0 ty) (tshift-correct 0 ty1))
                (lambda (ty2) (gen:const (just (cons ty1 ty2)))))]))))


(define/contract (gen:exact-term n e ty)
  (exact-integer? env? typ? . -> . gen?)
  (if (zero? n)
      (gen:exact-term0 e ty)
      (let (
        [g0 (gen:exact-term0 e ty)]
        [g1 (match ty
            [(Arr ty1 ty2)
             (gen:bind (gen:exact-term (- n 1) (EVar e ty1) ty2) (lambda (g) 
             (match g
                [(nothing) (gen:const (nothing))]
                [(just g) (gen:const (just (Abs ty1 g)))])))]
            [(All ty1 ty2) 
              (gen:bind (gen:exact-term (- n 1) (EBound e ty1) ty2) (lambda (g)
              (match g
                [(nothing) (gen:const (nothing))]
                [(just g) (gen:const (just (TAbs ty1 g)))])))]
            [_ (gen:const nothing)])]
        [g2 (gen:bind (gen:exact-typ (- n 1) e)
              (lambda (ty1) (gen:bind (gen:exact-term (- n 1) e (Arr ty1 ty))
              (lambda (t1) (gen:bind (gen:exact-term (- n 1) e ty1)
              (lambda (t2)
                (match (list t1 t2)
                  [(list (nothing) _) (gen:const (nothing))]
                  [(list _ (nothing)) (gen:const (nothing))]
                  [(list (just t1) (just t2)) (gen:const (just (App t1 t2)))]
                  )))))))]
        [g3 (gen:bind (gen:exact-typ (- n 1) e)
            (lambda (ty1) (gen:bind (gen:exact-term (- n 1) e (All ty1 (tshift-correct 0 ty)))
            (lambda (t1) (match t1
              [(nothing) (gen:const (nothing))]
              [(just t1) (gen:const (just (TApp t1 ty1)))])))))]
        [g4 (gen:bind (gen:replace ty)
            (lambda (tup) (match tup
              [(nothing) (gen:const (nothing))]
              [(just (cons ty2 ty12)) 
                (gen:bind (gen:exact-term (- n 1) e (All ty2 ty12))
                (lambda (t1) (match t1
                  [(nothing) (gen:const (nothing))]
                  [(just t1) (gen:const (just (TApp t1 ty2)))])))])))])
        (backtrack (list g0 g1 g2 g3 g4)))))


(define gen:term
    (gen:bind (gen:exact-typ 4 (Empty))
    (lambda (ty) (gen:exact-term 4 (Empty) ty))))

; (for ([i (in-range 10)])
;   (define start (current-inexact-milliseconds))
;   (sample gen:term 1)
;   (displayln (- (current-inexact-milliseconds) start)))

(define/contract (shrink:num n)
  (exact-integer? . -> . (listof exact-integer?))
  (if (<= n 0)
      '()
      (list (sub1 n))))

; shrinkType :: Type -> [Type]
; shrinkType Base = []
; shrinkType (t1 :-> t2) =
;   Base :
;   t1 :
;   t2 :
;   [t1' :-> t2 | t1' <- shrinkType t1]
;     ++ [t1 :-> t2' | t2' <- shrinkType t2]
; shrinkType (TVar n) = Base : [TVar n' | n' <- shrink n]
; shrinkType (ForAll t) = Base : t : [ForAll t' | t' <- shrinkType t]

(define/contract (shrink:typ ty)
  (typ? . -> . (listof typ?))
    (match ty
      [(Top) '()]
      [(Arr ty1 ty2) (append
        (list (Top) ty1 ty2)
        (map (lambda (ty1^) (Arr ty1^ ty2)) (shrink:typ ty1))
        (map (lambda (ty2^) (Arr ty1 ty2^)) (shrink:typ ty2)))]
      [(TVar n) (append
        (list (Top))
        (map (lambda (n^) (TVar n^)) (shrink:num n)))]
      [(All ty1 ty2) (append
        (list (Top) ty1 ty2)
        (map (lambda (ty1^) (All ty1^ ty2)) (shrink:typ ty1))
        (map (lambda (ty2^) (All ty1 ty2^)) (shrink:typ ty2)))]))

; shrinkExpr' Con = []
; shrinkExpr' (Var n) = Con : [Var n' | n' <- shrink n]
; shrinkExpr' (Lam t e) =
;   Con :
;   e :
;   [Lam t' e | t' <- shrinkType t]
;     ++ [Lam t e' | e' <- shrinkExpr' e]
; shrinkExpr' (e1 :@: e2) = Con : e1 : e2 : [e1' :@: e2 | e1' <- shrinkExpr' e1] ++ [e1 :@: e2' | e2' <- shrinkExpr' e2]
; shrinkExpr' (Cond e1 e2 e3) = Con : e1 : e2 : e3 : [Cond e1' e2 e3 | e1' <- shrinkExpr' e1] ++ [Cond e1 e2' e3 | e2' <- shrinkExpr' e2] ++ [Cond e1 e2 e3' | e3' <- shrinkExpr' e3]
; shrinkExpr' BTrue = [Con]
; shrinkExpr' BFalse = [Con, BTrue]
; shrinkExpr' (TLam e) = Con : e : [TLam e' | e' <- shrinkExpr' e]
; shrinkExpr' (TApp e t) = Con : e : [TApp e' t | e' <- shrinkExpr' e] ++ [TApp e t' | t' <- shrinkType t]

; shrinkExpr :: _ => Expr -> [Expr]
; shrinkExpr e =
;   [e' | e' <- shrinkExpr' e, wellTyped e']
;     ++ [e'' | e' <- shrinkExpr' e, e'' <- shrinkExpr' e', wellTyped e'']
;     ++ [e' | Just e' <- [step e], size e' < size e] --, typeOf e' = typeOf e]

(define/contract (shrink:term^ e)
  (term? . -> . (listof term?))
    (match e
      [(Var n) (map (lambda (n^) (Var n^)) (shrink:num n))]
      [(Abs ty e) (append
        (list e)
        (map (lambda (ty^) (Abs ty^ e)) (shrink:typ ty))
        (map (lambda (e^) (Abs ty e^)) (shrink:term^ e)))]
      [(App e1 e2) (append
        (list e1 e2)
        (map (lambda (e1^) (App e1^ e2)) (shrink:term^ e1))
        (map (lambda (e2^) (App e1 e2^)) (shrink:term^ e2)))]
      [(TAbs ty e) (append
        (list e)
        (map (lambda (ty^) (TAbs ty^ e)) (shrink:typ ty))
        (map (lambda (e^) (TAbs ty e^)) (shrink:term^ e)))]
      [(TApp e ty) (append
        (list e)
        (map (lambda (e^) (TApp e^ ty)) (shrink:term^ e))
        (map (lambda (ty^) (TApp e ty^)) (shrink:typ ty)))]))

(define/contract (well-typed? t)
  (term? . -> . boolean?)
  (let ([result (get-typ 40 (Empty) t)])
    (match result
      [(nothing) #f]
      [(just _) #t])))

(define/contract (size term)
  (term? . -> . number?)
  (match term
    [(Abs _ t) (+ 1 (size t))]
    [(App t1 t2) (+ 1 (size t1) (size t2))]
    [(TAbs _ t) (+ 1 (size t))]
    [(TApp t _) (+ 1 (size t))]
    [_ 1]
    )
  )

(define/contract (shrink:term e)
  ((maybe/c term?) . -> . (listof (maybe/c term?)))
  (match e
    [(nothing) '()]
    [(just e) (map 
                (lambda (e^) (just e^))
              (append
                (filter (lambda (e^) (well-typed? e^)) (shrink:term^ e))
                (filter (lambda (e^) (well-typed? e^)) (apply append (map shrink:term^ (shrink:term^ e))))
                (match (pstep/correct e)
                  [(nothing) '()]
                  [(just e^) (if (< (size e^) (size e)) (list e^) '())])
                  ))]))

(provide 
    gen:term
    shrink:term
)