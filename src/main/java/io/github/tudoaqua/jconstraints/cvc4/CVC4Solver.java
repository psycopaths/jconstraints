/**
 * Copyright 2020 TU Dortmund, Nils Schmidt und Malte Mues
 * <p>
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * <p>
 * http://www.apache.org/licenses/LICENSE-2.0
 * <p>
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */
package io.github.tudoaqua.jconstraints.cvc4;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class CVC4Solver extends ConstraintSolver{
	
	ExprManager em;
	SmtEngine smt;
	


  private static void prefixPrintGetValue(SmtEngine smt, Expr e, int level) {
    for(int i = 0; i < level; ++i) { System.out.print('-'); }
    System.out.println("smt.getValue(" + e + ") -> " + smt.getValue(e));

    if(e.hasOperator()) {
      prefixPrintGetValue(smt, e.getOperator(), level + 1);
    }

    for(int i = 0; i < e.getNumChildren(); ++i) {
      Expr curr = e.getChild(i);
      prefixPrintGetValue(smt, curr, level + 1);
    }
  }

	
	public CVC4Solver(Map<String, String> options) {
		em = new ExprManager();
		smt = new SmtEngine(em);
		//smt.setLogic("QF_NRA");

		smt.setOption("produce-models", new SExpr(true)); // Produce Models
		smt.setOption("output-language", new SExpr("cvc4")); // output-language
		smt.setOption("default-dag-thresh", new SExpr(0));
	}
	
	
	@Override
	public Result solve(Expression<Boolean> f, Valuation result) {
		CVC4ExpressionGenerator gen = new CVC4ExpressionGenerator(em);
		Expr expr = gen.generateExpression(f);

		//System.out.println("Class expr: "+expr.getClass());
		smt.assertFormula(expr);
		Result resJC = Result.DONT_KNOW;
		edu.nyu.acsys.CVC4.Result resCVC = smt.checkSat(em.mkConst(true));

		if (resCVC.toString().equals("sat")) {
			prefixPrintGetValue(smt, expr, 0);
		}
		if (resCVC.toString().equals("sat")) {
			resJC = Result.SAT;
			HashMap<String, Expr> vars = gen.getVars();
			Set<Variable<?>> jConstraintsVars = ExpressionUtil.freeVariables(f);
			for (Variable var : jConstraintsVars) {
				Expr cvc4Var = vars.get(var.getName());
				Object val = smt.getValue(cvc4Var);
				result.setValue(var, val);
			}

		} else if (resCVC.toString().equals("unsat")) {
			resJC = Result.UNSAT;
		}

		return resJC;
	}

}
