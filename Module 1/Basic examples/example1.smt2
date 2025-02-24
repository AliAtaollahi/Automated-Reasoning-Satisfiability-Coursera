(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert
(and (> (* 2 a) (+ b c)) (> (* 2 b) (+ c d))
(> (* 2 c) (* 3 d)) (> (* 3 d) (+ a c))))
(check-sat)
(get-model)

