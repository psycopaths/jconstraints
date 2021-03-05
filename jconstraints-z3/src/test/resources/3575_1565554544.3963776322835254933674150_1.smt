;  depth   = 3
;  nconst  = 5
;  assertions = 5
;  timeout = 2500
;  time    = {'smt_solvers/QF_S/cvc4/': 0.06158018112182617, 'smt_solvers/QF_S/z3str3fed/': 0.0691978931427002, 'smt_solvers/QF_S/z3str3/': 0.08379268646240234, 'smt_solvers/QF_S/z3seq/': 0.08653044700622559}
;  score   = -0.024950265884399414
;  stdout  = {'smt_solvers/QF_S/cvc4/': 'unsat', 'smt_solvers/QF_S/z3str3fed/': 'unsat', 'smt_solvers/QF_S/z3str3/': 'unsat', 'smt_solvers/QF_S/z3seq/': 'unsat'}
(set-logic QF_S)(declare-fun var0 () String)(declare-fun var1 () String)(declare-fun var2 () String)(declare-fun var3 () String)(declare-fun var4 () String)(declare-fun var5 () Int)(declare-fun var6 () Int)(declare-fun var7 () Int)(declare-fun var8 () Int)(declare-fun var9 () Int)(declare-fun var10 () Bool)(declare-fun var11 () Bool)(declare-fun var12 () Bool)(declare-fun var13 () Bool)(declare-fun var14 () Bool)(assert (str.in.re "vN81cwz%by" re.allchar))(assert (str.contains var2 var3))(assert (<= (str.len "L!n`4F<Z%d") (str.len (str.substr var2 var7 var6))))(assert (>= var6 5))(assert (not var13))(check-sat)