/*
 * Copyright (C) 2015, United States Government, as represented by the 
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment 
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you 
 * may not use this file except in compliance with the License. You may obtain a 
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software distributed 
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR 
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the 
 * specific language governing permissions and limitations under the License.
 */
package gov.nasa.jpf.constraints.expressions;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseDoubleException;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Properties;
import java.util.Set;

public class ExpressionZ3Test   {

  @Test
  public void expressionTest()throws ImpreciseRepresentationException, ImpreciseDoubleException {

	/*
    if (args.length < 1) {
      System.out.println("Usage: ExpressionsExampleZ3 [path to libZ3Java]");
      return;
    }*/

    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "NativeZ3");


    // construct expression

    Variable<Double> var_i1 = Variable.create(BuiltinTypes.DOUBLE, "i1");
    Variable<Double> var_i2 = Variable.create(BuiltinTypes.DOUBLE, "i2");

    Constant<Double> const_5 = Constant.create(BuiltinTypes.DOUBLE, 0.000000052);
    Constant<Double> const_10 = Constant.create(BuiltinTypes.DOUBLE, 0.000000101);

    System.out.println("c1:" + const_5.getValue());
    System.out.println("c2:" + const_10.getValue());

    NumericCompound<Double> inner = NumericCompound.create(var_i1, NumericOperator.PLUS, const_5);

    NumericCompound<Double> outer = NumericCompound.create(inner, NumericOperator.MUL, var_i2);

    NumericBooleanExpression expr = NumericBooleanExpression.create(outer, NumericComparator.GT, const_10);

    System.out.println(expr);

    // get names

    Set<Variable<?>> vars = new HashSet<Variable<?>>();
    expr.collectFreeVariables(vars);

    // renaming

    RenameMap rename = new RenameMap();
    System.out.print("Names: ");
    int i = 0;
    for (Variable<?> var : vars) {
      System.out.print(var.getName() + " ");
      rename.put(var.getName(), "int_" + i++);

    }
    System.out.println();
    Expression<Boolean> expr2 = ExpressionUtil.renameVars(expr, rename).requireAs(BuiltinTypes.BOOL);
    System.out.println(expr2);

    // replacement

    Map<Expression, Expression> replace = new HashMap<>();
    replace.put(outer, inner);
    Expression<Boolean> expr3 = expr.replaceTerms(replace).requireAs(BuiltinTypes.BOOL);
    System.out.println(expr3);

    // solve

//    m.setIntMin(0);
//    m.setVarMax(var_i1, 0.100);

    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
    ConstraintSolver solver = factory.createSolver();

    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(expr, val);
    System.out.println(result);
    System.out.println(val);

    Valuation val2 = new Valuation();
    ConstraintSolver.Result result2 = solver.solve(expr3, val2);
    System.out.println(result2);
    System.out.println(val2);

  }

  private class RenameMap extends HashMap<String, String> implements Function<String, String> {

    @Override
    public String apply(String variable) {
      return getOrDefault(variable, variable);
    }
  }

}
