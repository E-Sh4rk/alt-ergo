(set-logic ALL)

(declare-datatypes
 ((s 2) (t 2))
 ((par (I J) ((A (sel_A1 I) (sel_A2 Int))
              (B (sel_B1 J))
              (C (sel_C1 (t J I)) (sel_C2 Bool))))
  (par (K L) ((X (sel_X1 K) (sel_X2 (s K Int)))
              (Y (sel_Y1 Real) (sel_Y2 L))))))


(declare-sort u 0)
(declare-sort v 0)

(declare-const a (s u v))
(declare-const b (t u u))
(declare-const c u)

(assert (=> (=> (not ((_ is A) a)) (not ((_ is B) a))) ((_ is C) a)))


(declare-const x Bool)
;(assert (=> (=> (not ((_ is A) x)) (not ((_ is B) x))) ((_ is C) x)))

(assert (=> (= b (Y 0. c)) (not (and ((_ is X) b) (>= (sel_Y1 b) 0.)))))

(check-sat)
