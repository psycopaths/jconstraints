/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.Set;
import org.testng.annotations.Test;

public class LetExpressionTest {

  Variable x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable x1 = Variable.create(BuiltinTypes.SINT32, "x1");
  Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
  Constant c = Constant.create(BuiltinTypes.SINT32, 5);
  Expression<Boolean> expr = NumericBooleanExpression.create(x, NumericComparator.GT, c);
  Constant c4 = Constant.create(BuiltinTypes.SINT32, 4);
  LetExpression letExpr = LetExpression.create(x, c4, expr);

  @Test(groups = {"expressions", "base"})
  public void LetExpressionAcceptsVisitorTest() {
    DummyVisitorForTest visitor = new DummyVisitorForTest();
    assertEquals(letExpr.accept(visitor, false), letExpr);
  }

  @Test(groups = {"expressions", "base"})
  public void LetExpressionEvaluation1Test() {
    Valuation val1 = new Valuation();
    val1.setValue(x, 6);

    Valuation val2 = new Valuation();
    val2.setValue(x, 4);

    Valuation val3 = new Valuation();
    val3.setValue(x, 6);

    assertTrue(expr.evaluate(val1));
    assertFalse(letExpr.evaluate(val2));
    assertFalse(letExpr.evaluate(val3));
  }

  @Test(groups = {"expressions", "base"})
  public void flattenLetExpression1Test() {
    Expression expectedOutcome = NumericBooleanExpression.create(c4, NumericComparator.GT, c);
    assertEquals(letExpr.flattenLetExpression(), expectedOutcome);
  }

  @Test(groups = {"expressions", "base"})
  public void flattenLetExpression2Test() {
    Constant c2 = Constant.create(BuiltinTypes.SINT32, 2);
    NumericBooleanExpression partA = NumericBooleanExpression.create(x1, NumericComparator.LE, c4);
    NumericCompound replacement = NumericCompound.create(x2, NumericOperator.PLUS, c2);

    LetExpression expr = LetExpression.create(x1, replacement, partA);

    Expression expectedOutcome =
        NumericBooleanExpression.create(replacement, NumericComparator.LE, c4);

    assertEquals(expr.flattenLetExpression(), expectedOutcome);

    Variable x3 = Variable.create(BuiltinTypes.BOOL, "x3");
    Expression expr2 = PropositionalCompound.create(x3, LogicalOperator.AND, expr);

    Variable x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    NumericBooleanExpression replacementB =
        NumericBooleanExpression.create(x4, NumericComparator.GT, c2);
    LetExpression let2 = LetExpression.create(x3, replacementB, expr2);

    Expression expectedOutcome2 =
        PropositionalCompound.create(replacementB, LogicalOperator.AND, expectedOutcome);

    System.out.println(let2);
    System.out.println(let2.flattenLetExpression());

    assertEquals(let2.flattenLetExpression(), expectedOutcome2);
  }

  @Test(groups = {"expressions", "base"})
  public void chainedLetExpressionFlattening01Test() {
    NumericCompound nc = NumericCompound.create(x, NumericOperator.PLUS, c4);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x1, EQ, x2);
    LetExpression inner = LetExpression.create(x1, nc, nbe);
    Variable x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    LetExpression outter = LetExpression.create(x, x4, inner);
    Expression flattened = outter.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flattened);
    assertFalse(vars.contains(x), "the x should be replaced by x4");
    assertFalse(vars.contains(x1), "The x1 should be replaced by the numeric compound");
    assertTrue(vars.contains(x4), "The x4 is very present now");
  }

  public class DummyVisitorForTest extends AbstractExpressionVisitor<Expression, Boolean> {

    @Override
    protected Expression defaultVisit(Expression expression, Boolean data) {
      return expression;
    }
  }
}
