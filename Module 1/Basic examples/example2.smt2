(declare-const A Bool)
(declare-const B Bool)
(declare-const C Bool)
(declare-const D Bool)
(assert
(and
(iff A (and D B))
(implies C B)
(not (or A B (not D)))
(or (and (not A) C) D)
))
(check-sat)
(get-model)