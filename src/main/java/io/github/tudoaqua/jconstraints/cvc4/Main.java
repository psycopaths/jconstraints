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

import java.util.Properties;


import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class Main {
	public static void main(String[] args) {
		 Variable x = new Variable(BuiltinTypes.INTEGER, "x");
		    Variable a = new Variable(BuiltinTypes.INTEGER, "a");
		    Variable b = new Variable(BuiltinTypes.INTEGER, "b");

		    Constant zero = new Constant(BuiltinTypes.INTEGER, 0);

		    Expression<Boolean> expr = new NumericBooleanExpression(
		            x, 
		            NumericComparator.EQ,
		            new NumericCompound<>(a, NumericOperator.PLUS, b));                

		    expr = ExpressionUtil.and(expr,
		            new NumericBooleanExpression(a, NumericComparator.GT, zero),
		            new NumericBooleanExpression(b, NumericComparator.LT, zero));
		    System.out.println(expr);
		    Properties conf = new Properties();     
	        conf.setProperty("symbolic.dp", "cvc4");
	        conf.setProperty("cvc4.options", "cvc4Logic=QF_LIRA");
	        ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	        factory.registerProvider(new CVC4SolverProvider());
	        ConstraintSolver solver = factory.createSolver();
	        Valuation val = new Valuation();
	        Result result=solver.solve(expr, val);
	        System.out.println("Result: "+result.toString());
		}
	}
