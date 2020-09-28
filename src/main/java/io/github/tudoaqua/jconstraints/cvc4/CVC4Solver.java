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

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.apache.commons.math3.fraction.BigFractionFormat;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

public class CVC4Solver extends ConstraintSolver {

	private final ExprManager em;
	private final SmtEngine smt;
	private final CVC4ExpressionGenerator gen;

	public CVC4Solver(Map<String, String> options) {
		em = new ExprManager();
		smt = new SmtEngine(em);
		gen = new CVC4ExpressionGenerator(em);

		smt.setOption("produce-models", new SExpr(true));
		smt.setOption("output-language", new SExpr("cvc4"));
	}

	@Override
	public Result solve(Expression<Boolean> f, Valuation result) {
		gen.clearVars();
		Expr expr = gen.generateExpression(f);
		edu.stanford.CVC4.Result resCVC = smt.checkSat(expr);
		Result resJC = CVC4Solver.convertCVC4Res(resCVC);
		if (resJC.equals(Result.SAT)) {
			getModel(result, gen.getVars(), smt);
		}
		return resJC;
	}

	@Override
	public Result isSatisfiable(Expression<Boolean> f) {
		edu.stanford.CVC4.Result cvc4Res = smt.checkSat(gen.generateExpression(f));
		return CVC4Solver.convertCVC4Res(cvc4Res);
	}

	@Override
	public SolverContext createContext() {
		return new CVC4SolverContext();
	}

	@Override
	public String getName() {
		return super.getName();
	}

	public static ConstraintSolver.Result convertCVC4Res(edu.stanford.CVC4.Result res) {
		if (res.toString().toLowerCase().equals("sat")) {
			return Result.SAT;
		} else if (res.toString().toLowerCase().equals("unsat")) {
			return Result.UNSAT;
		} else {
			return Result.DONT_KNOW;
		}
	}

	public static void getModel(Valuation val, HashMap<Variable, Expr> vars, SmtEngine smt) {
		if (val != null) {
			for (Map.Entry<Variable, Expr> entry : vars.entrySet()) {
				Expr value = smt.getValue(entry.getValue());
				if (value.isConst()) {
					Kind k = value.getKind();
					String valueString = value.toString().replace("(", "").replace(")", "").replace(" ", "");
					if (Kind.CONST_RATIONAL.equals(k)) {
						if (entry.getKey().getType().equals(BuiltinTypes.INTEGER)) {
							val.setValue(entry.getKey(), new BigInteger(valueString));
						} else {
							val.setValue(entry.getKey(), BigFractionFormat.getProperInstance().parse(valueString));
						}
					} else if (Kind.CONST_FLOATINGPOINT.equals(k)) {
						val.setValue(entry.getKey(), new BigDecimal(valueString));
					} else if (Kind.CONST_BITVECTOR.equals(k)) {
						val.setValue(entry.getKey(), new BigInteger(valueString));
					} else if (Kind.CONST_BOOLEAN.equals(k)) {
						val.setValue(entry.getKey(), new Boolean(valueString).booleanValue());
					} else {
						throw new IllegalArgumentException("Cannot parse the variable of the model");
					}
				}
			}
		}
	}
}
