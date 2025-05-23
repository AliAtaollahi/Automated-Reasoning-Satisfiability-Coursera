(set-option :produce-models true)
(set-logic QF_LIA)

; Each truck i has integer variables:
;   x_n_i = # of nuzzles, x_p_i = # of prittles, x_s_i = # of skipples,
;   x_c_i = # of crottles, x_d_i = # of duppies.
; We'll declare them for i=1..8.
(declare-const x_n1 Int)
(declare-const x_p1 Int)
(declare-const x_s1 Int)
(declare-const x_c1 Int)
(declare-const x_d1 Int)
(declare-const x_n2 Int)
(declare-const x_p2 Int)
(declare-const x_s2 Int)
(declare-const x_c2 Int)
(declare-const x_d2 Int)
(declare-const x_n3 Int)
(declare-const x_p3 Int)
(declare-const x_s3 Int)
(declare-const x_c3 Int)
(declare-const x_d3 Int)
(declare-const x_n4 Int)
(declare-const x_p4 Int)
(declare-const x_s4 Int)
(declare-const x_c4 Int)
(declare-const x_d4 Int)
(declare-const x_n5 Int)
(declare-const x_p5 Int)
(declare-const x_s5 Int)
(declare-const x_c5 Int)
(declare-const x_d5 Int)
(declare-const x_n6 Int)
(declare-const x_p6 Int)
(declare-const x_s6 Int)
(declare-const x_c6 Int)
(declare-const x_d6 Int)
(declare-const x_n7 Int)
(declare-const x_p7 Int)
(declare-const x_s7 Int)
(declare-const x_c7 Int)
(declare-const x_d7 Int)
(declare-const x_n8 Int)
(declare-const x_p8 Int)
(declare-const x_s8 Int)
(declare-const x_c8 Int)
(declare-const x_d8 Int)

; Domain constraints: all variables ≥ 0.
(assert (and
  (>= x_n1 0)
  (>= x_p1 0)
  (>= x_s1 0)
  (>= x_c1 0)
  (>= x_d1 0)
  (>= x_n2 0)
  (>= x_p2 0)
  (>= x_s2 0)
  (>= x_c2 0)
  (>= x_d2 0)
  (>= x_n3 0)
  (>= x_p3 0)
  (>= x_s3 0)
  (>= x_c3 0)
  (>= x_d3 0)
  (>= x_n4 0)
  (>= x_p4 0)
  (>= x_s4 0)
  (>= x_c4 0)
  (>= x_d4 0)
  (>= x_n5 0)
  (>= x_p5 0)
  (>= x_s5 0)
  (>= x_c5 0)
  (>= x_d5 0)
  (>= x_n6 0)
  (>= x_p6 0)
  (>= x_s6 0)
  (>= x_c6 0)
  (>= x_d6 0)
  (>= x_n7 0)
  (>= x_p7 0)
  (>= x_s7 0)
  (>= x_c7 0)
  (>= x_d7 0)
  (>= x_n8 0)
  (>= x_p8 0)
  (>= x_s8 0)
  (>= x_c8 0)
  (>= x_d8 0)
))

; Total item constraints:
; 4 nuzzles, 8 skipples, 10 crottles, 7 tynnels, 20 duppies
(assert (= (+ x_n1 x_n2 x_n3 x_n4 x_n5 x_n6 x_n7 x_n8) 4))
(assert (= (+ x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8) 8))
(assert (= (+ x_c1 x_c2 x_c3 x_c4 x_c5 x_c6 x_c7 x_c8) 10))
(assert (= (+ x_d1 x_d2 x_d3 x_d4 x_d5 x_d6 x_d7 x_d8) 20))

; We want to maximize prittles, so no fixed total for x_p_i.

; Skipples need cooling: only 3 of the 8 trucks are cooled.
; For simplicity, assume trucks 1,2,3 are cooled; set x_s4..x_s8 = 0:
(assert (= x_s4 0))
(assert (= x_s5 0))
(assert (= x_s6 0))
(assert (= x_s7 0))
(assert (= x_s8 0))

; Each truck’s capacity ≤ 8000 kg, and ≤ 8 pallets:
(assert (<= (+ (* 800 x_n1) (* 1100 x_p1) (* 1000 x_s1) (* 2500 x_c1) (* 200 x_d1)) 8000))
(assert (<= (+ x_n1 x_p1 x_s1 x_c1 x_d1) 8))
(assert (<= (+ (* 800 x_n2) (* 1100 x_p2) (* 1000 x_s2) (* 2500 x_c2) (* 200 x_d2)) 8000))
(assert (<= (+ x_n2 x_p2 x_s2 x_c2 x_d2) 8))
(assert (<= (+ (* 800 x_n3) (* 1100 x_p3) (* 1000 x_s3) (* 2500 x_c3) (* 200 x_d3)) 8000))
(assert (<= (+ x_n3 x_p3 x_s3 x_c3 x_d3) 8))
(assert (<= (+ (* 800 x_n4) (* 1100 x_p4) (* 1000 x_s4) (* 2500 x_c4) (* 200 x_d4)) 8000))
(assert (<= (+ x_n4 x_p4 x_s4 x_c4 x_d4) 8))
(assert (<= (+ (* 800 x_n5) (* 1100 x_p5) (* 1000 x_s5) (* 2500 x_c5) (* 200 x_d5)) 8000))
(assert (<= (+ x_n5 x_p5 x_s5 x_c5 x_d5) 8))
(assert (<= (+ (* 800 x_n6) (* 1100 x_p6) (* 1000 x_s6) (* 2500 x_c6) (* 200 x_d6)) 8000))
(assert (<= (+ x_n6 x_p6 x_s6 x_c6 x_d6) 8))
(assert (<= (+ (* 800 x_n7) (* 1100 x_p7) (* 1000 x_s7) (* 2500 x_c7) (* 200 x_d7)) 8000))
(assert (<= (+ x_n7 x_p7 x_s7 x_c7 x_d7) 8))
(assert (<= (+ (* 800 x_n8) (* 1100 x_p8) (* 1000 x_s8) (* 2500 x_c8) (* 200 x_d8)) 8000))
(assert (<= (+ x_n8 x_p8 x_s8 x_c8 x_d8) 8))

; Nuzzle constraint: at most 2 nuzzles per truck:
(assert (<= x_n1 1))
(assert (<= x_n2 1))
(assert (<= x_n3 1))
(assert (<= x_n4 1))
(assert (<= x_n5 1))
(assert (<= x_n6 1))
(assert (<= x_n7 1))
(assert (<= x_n8 1))

; No prittles and crottles together
(assert (or (= x_p1 0) (= x_c1 0)))
(assert (or (= x_p2 0) (= x_c2 0)))
(assert (or (= x_p3 0) (= x_c3 0)))
(assert (or (= x_p4 0) (= x_c4 0)))
(assert (or (= x_p5 0) (= x_c5 0)))
(assert (or (= x_p6 0) (= x_c6 0)))
(assert (or (= x_p7 0) (= x_c7 0)))
(assert (or (= x_p8 0) (= x_c8 0)))

; Objective: maximize the total number of prittles
(maximize (+ x_p1 x_p2 x_p3 x_p4 x_p5 x_p6 x_p7 x_p8))

(check-sat)
(get-objectives)
(get-model)