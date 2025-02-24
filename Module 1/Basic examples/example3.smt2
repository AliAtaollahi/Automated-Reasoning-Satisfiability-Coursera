(declare-fun f (Int) Int)
(assert
(and
(> (* 2 (f 1)) (+ (f 2) (f 3)))
(> (* 2 (f 2)) (+ (f 3) (f 4)))
(> (* 2 (f 3)) (* 3 (f 4)))
(> (* 3 (f 4)) (+ (f 1) (f 3)))))
(check-sat)
(get-model)
