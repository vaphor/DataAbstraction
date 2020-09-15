(declare-rel start ((Array Int Int) Int))
(declare-rel assert2 ((Array Int Int) Int))
(declare-rel assign ((Array Int Int) Int))
;
(assert (forall ((a (Array Int Int)) (i Int)) (start a i)))
(assert (forall ((a (Array Int Int)) (i Int)) (=> (start a i) (assign a 0))))
(assert (forall ((a (Array Int Int)) (i Int) (v Int)) (=> (and (assign a i) (= v (select a i))) (assert2 a v))))
(assert (forall ((a (Array Int Int)) (i Int) (v Int)) (=> (assert2 a v) (= v (select a 0)))))
(check-sat)
