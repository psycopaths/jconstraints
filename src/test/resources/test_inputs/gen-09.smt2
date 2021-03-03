(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* 2 a) 1))
(assert (= (* b b) 2))
(assert (> b a))
(check-sat)
(exit)
