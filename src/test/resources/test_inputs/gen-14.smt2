(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () Real)
(assert (= (* a a) (- 3)))
(check-sat)
(exit)
