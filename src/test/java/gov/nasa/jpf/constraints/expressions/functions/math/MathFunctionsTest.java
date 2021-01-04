/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.expressions.functions.math;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.lang.reflect.Method;
import java.util.Random;
import org.testng.Assert;
import org.testng.annotations.Test;

@Test
public class MathFunctionsTest {

  private static final Random random = new Random();

  private static final Variable<Double> VAR_X = Variable.create(BuiltinTypes.DOUBLE, "x");
  private static final Variable<Double> VAR_Y = Variable.create(BuiltinTypes.DOUBLE, "y");

  private static final Expression<Double> EXPR =
      NumericCompound.create(VAR_X, NumericOperator.PLUS, VAR_Y);

  private static Valuation createValuation() {
    // Make sure result value is in interval (0, 1)
    double x = random.nextDouble() * 0.9 + 0.1;
    double y = -(random.nextDouble() * 0.9 + 0.1) * x * 0.5;
    Valuation val = new Valuation();
    val.setValue(VAR_X, x);
    val.setValue(VAR_Y, y);

    return val;
  }

  private static double directEval(Function<Double> func, double arg) throws Exception {
    Method m = Math.class.getMethod(func.getName(), double.class);

    return (Double) m.invoke(null, arg);
  }

  @Test
  public void testCos() throws Exception {
    testMathFunction(MathFunctions.COS);
  }

  @Test
  public void testSin() throws Exception {
    testMathFunction(MathFunctions.SIN);
  }

  @Test
  public void testTan() throws Exception {
    testMathFunction(MathFunctions.TAN);
  }

  @Test
  public void testAcos() throws Exception {
    testMathFunction(MathFunctions.ACOS);
  }

  @Test
  public void testAsin() throws Exception {
    testMathFunction(MathFunctions.ASIN);
  }

  @Test
  public void testAtan() throws Exception {
    testMathFunction(MathFunctions.ATAN);
  }

  private void testMathFunction(Function<Double> function) throws Exception {
    Expression<Double> expr = EXPR;
    Valuation val = createValuation();

    double exprEval = expr.evaluate(val);
    Expression<Double> funcExpr = new FunctionExpression<>(function, expr);

    double funcEval = funcExpr.evaluate(val);

    double directEval = directEval(function, exprEval);

    Assert.assertEquals(directEval, funcEval);
  }
}
