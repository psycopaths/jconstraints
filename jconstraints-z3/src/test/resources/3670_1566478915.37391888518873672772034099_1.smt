;  depth   = 3
;  nconst  = 6
;  assertions = 7
;  timeout = 2500
;  time    = {'smt_solvers/QF_S/z3str3fed/': 0.0738074779510498, 'smt_solvers/QF_S/z3str3/': 0.11449003219604492, 'smt_solvers/QF_S/z3seq/': 0.09204363822937012, 'smt_solvers/QF_S/cvc4/': 0.24636626243591309}
;  score   = 0.13187623023986816
;  stdout  = {'smt_solvers/QF_S/z3str3fed/': 'unsat', 'smt_solvers/QF_S/z3str3/': 'unsat', 'smt_solvers/QF_S/z3seq/': 'unsat', 'smt_solvers/QF_S/cvc4/': 'unsat'}
(set-logic QF_S)(declare-fun var0 () String)(declare-fun var1 () String)(declare-fun var2 () String)(declare-fun var3 () String)(declare-fun var4 () String)(declare-fun var5 () String)(declare-fun var6 () Int)(declare-fun var7 () Int)(declare-fun var8 () Int)(declare-fun var9 () Int)(declare-fun var10 () Int)(declare-fun var11 () Int)(declare-fun var12 () Bool)(declare-fun var13 () Bool)(declare-fun var14 () Bool)(declare-fun var15 () Bool)(declare-fun var16 () Bool)(declare-fun var17 () Bool)(assert (> var8 var10))(assert (str.suffixof (str.substr (str.at var0 var10) (str.len var4) (str.indexof var5 var4 var9)) (str.at "b,9L/LUM/r" var10)))(assert (not (not var14)))(assert (> (str.len var4) (str.indexof "uUZPanrBqO" var2 var7)))(assert (str.in.re var3 re.allchar))(assert (str.in.re (str.at var2 var9) (re.++ re.allchar re.allchar)))(assert (< var9 0))(check-sat)