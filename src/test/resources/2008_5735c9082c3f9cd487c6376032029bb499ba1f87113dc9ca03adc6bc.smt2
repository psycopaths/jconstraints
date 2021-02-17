
(declare-fun K () Int)

(assert (and (not (not (= (ite (< (mod 7 K) 7) 1 0) 0))) (not (not (= (ite (= (mod 7 K) 0) 1 0) 0)))))

(check-sat)

;(get-value (K))





