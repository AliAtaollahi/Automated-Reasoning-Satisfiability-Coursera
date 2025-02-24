(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(assert (and
(= A 98798798987987987987987923423)
(= B 763429999988888888887364578645)
(= (+ (* 87 A) (* 93 B)) (+ C C))))
(check-sat)
(get-model)
