
; SMT Constraints

(declare-fun T () Int)


;; Parameter n (in 1..10)
(declare-const n Int)
(assert (not (= n 10)))
(assert (and (>= n 1) (<= n 10)))

;; Initial state
(declare-const a0 Int)
(declare-const b0 Int)
(assert (= a0 1))
(assert (= b0 1))

(declare-const c1 Bool)
(declare-const a1 Int)
(declare-const b1 Int)

(declare-const c2 Bool)
(declare-const a2 Int)
(declare-const b2 Int)

(declare-const c3 Bool)
(declare-const a3 Int)
(declare-const b3 Int)

(declare-const c4 Bool)
(declare-const a4 Int)
(declare-const b4 Int)

(declare-const c5 Bool)
(declare-const a5 Int)
(declare-const b5 Int)

(declare-const c6 Bool)
(declare-const a6 Int)
(declare-const b6 Int)

(declare-const c7 Bool)
(declare-const a7 Int)
(declare-const b7 Int)

(declare-const c8 Bool)
(declare-const a8 Int)
(declare-const b8 Int)

(declare-const c9 Bool)
(declare-const a9 Int)
(declare-const b9 Int)

(declare-const c10 Bool)
(declare-const a10 Int)
(declare-const b10 Int)



;; Iteration 1
(assert (ite c1 
              (and (= a1 (+ a0 (* 2 b0)))  ; then: a := a + 2*b
                   (= b1 (+ b0 1)))        ; b := b + i
              (and (= a1 (+ a0 1))          ; else: a := a + i
                   (= b1 (+ a0 b0)))))

;; Iteration 2
(assert (ite c2 
              (and (= a2 (+ a1 (* 2 b1)))  ; then: a := a + 2*b
                   (= b2 (+ b1 2)))        ; b := b + i
              (and (= a2 (+ a1 2))          ; else: a := a + i
                   (= b2 (+ a1 b1)))))

;; Iteration 3
(assert (ite c3 
              (and (= a3 (+ a2 (* 2 b2)))  ; then: a := a + 2*b
                   (= b3 (+ b2 3)))        ; b := b + i
              (and (= a3 (+ a2 3))          ; else: a := a + i
                   (= b3 (+ a2 b2)))))

;; Iteration 4
(assert (ite c4 
              (and (= a4 (+ a3 (* 2 b3)))  ; then: a := a + 2*b
                   (= b4 (+ b3 4)))        ; b := b + i
              (and (= a4 (+ a3 4))          ; else: a := a + i
                   (= b4 (+ a3 b3)))))

;; Iteration 5
(assert (ite c5 
              (and (= a5 (+ a4 (* 2 b4)))  ; then: a := a + 2*b
                   (= b5 (+ b4 5)))        ; b := b + i
              (and (= a5 (+ a4 5))          ; else: a := a + i
                   (= b5 (+ a4 b4)))))

;; Iteration 6
(assert (ite c6 
              (and (= a6 (+ a5 (* 2 b5)))  ; then: a := a + 2*b
                   (= b6 (+ b5 6)))        ; b := b + i
              (and (= a6 (+ a5 6))          ; else: a := a + i
                   (= b6 (+ a5 b5)))))

;; Iteration 7
(assert (ite c7 
              (and (= a7 (+ a6 (* 2 b6)))  ; then: a := a + 2*b
                   (= b7 (+ b6 7)))        ; b := b + i
              (and (= a7 (+ a6 7))          ; else: a := a + i
                   (= b7 (+ a6 b6)))))

;; Iteration 8
(assert (ite c8 
              (and (= a8 (+ a7 (* 2 b7)))  ; then: a := a + 2*b
                   (= b8 (+ b7 8)))        ; b := b + i
              (and (= a8 (+ a7 8))          ; else: a := a + i
                   (= b8 (+ a7 b7)))))

;; Iteration 9
(assert (ite c9 
              (and (= a9 (+ a8 (* 2 b8)))  ; then: a := a + 2*b
                   (= b9 (+ b8 9)))        ; b := b + i
              (and (= a9 (+ a8 9))          ; else: a := a + i
                   (= b9 (+ a8 b8)))))

;; Iteration 10
(assert (ite c10 
              (and (= a10 (+ a9 (* 2 b9)))  ; then: a := a + 2*b
                   (= b10 (+ b9 10)))        ; b := b + i
              (and (= a10 (+ a9 10))          ; else: a := a + i
                   (= b10 (+ a9 b9)))))

;; Crash condition: crash if b10 equals 600+n.
(assert (= b10 (+ 600 n)))


(check-sat)
(get-model)
(exit)
