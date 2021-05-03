
(set-logic HORN)
(declare-fun FOR2 ((Array Int Int) Int Int) Bool)
(assert (forall ((a (Array Int Int)) (N Int) (k Int)) ( => (and (FOR2 a  N k ) (< k N)) (FOR2 (store a  k  (+ (select a  k ) 1)) N  (k+1) ))))
(check-sat)
