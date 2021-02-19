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

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
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
  Expression<Boolean> expr = NumericBooleanExpression.create(x, GT, c);
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
    Expression expectedOutcome = NumericBooleanExpression.create(c4, GT, c);
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
    Expression expr2 = PropositionalCompound.create(x3, AND, expr);

    Variable x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    NumericBooleanExpression replacementB = NumericBooleanExpression.create(x4, GT, c2);
    LetExpression let2 = LetExpression.create(x3, replacementB, expr2);

    Expression expectedOutcome2 =
        PropositionalCompound.create(replacementB, AND, expectedOutcome);

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

  @Test(groups = {"expressions", "base"})
  public void chainedLetExpressionFlattening02Test() {
    Variable y = Variable.create(BuiltinTypes.SINT32, "Y");

    NumericCompound nc = NumericCompound.create(x, NumericOperator.PLUS, c4);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x1, EQ, x2);
    LetExpression inner2 = LetExpression.create(y, nc, y);
    LetExpression inner = LetExpression.create(x1, inner2, nbe);
    Variable x4 = Variable.create(BuiltinTypes.SINT32, "x4");
    LetExpression outter = LetExpression.create(x, x4, inner);
    Expression flattened = outter.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flattened);
    assertFalse(vars.contains(x), "the x should be replaced by x4");
    assertFalse(vars.contains(x1), "The x1 should be replaced by the numeric compound");
    assertFalse(vars.contains(y), "The y should be replaced by the numeric compound");
    assertTrue(vars.contains(x4), "The x4 is very present now");
  }

  @Test(groups = {"expressions", "base"})
  public void letExpresisonsAndITE01Test() {
    Variable X = Variable.create(BuiltinTypes.SINT32, "X");
    Variable X1 = Variable.create(BuiltinTypes.SINT32, "X1");
    Variable B = Variable.create(BuiltinTypes.BOOL, "B");
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 5);
    IfThenElse ite = IfThenElse.create(B, X1, c1);
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(ite, GT, Constant.create(BuiltinTypes.SINT32, 6));
    LetExpression let = LetExpression.create(X1, X, nbe);
    Expression flat = let.flattenLetExpression();
    assertFalse(flat.toString().contains("X1"), "X1 should be replaced");
  }

  @Test(groups = {"expressions", "base"})
  public void letExpresisonsAndITE02Test() {
    Variable X = Variable.create(BuiltinTypes.BOOL, "X");
    Variable X1 = Variable.create(BuiltinTypes.BOOL, "X1");
    Variable X2 = Variable.create(BuiltinTypes.BOOL, "X2");
    Variable X3 = Variable.create(BuiltinTypes.BOOL, "X3");
    Variable X4 = Variable.create(BuiltinTypes.BOOL, "X4");
    Variable X5 = Variable.create(BuiltinTypes.BOOL, "X5");
    Variable X6 = Variable.create(BuiltinTypes.BOOL, "X6");
    Variable X7 = Variable.create(BuiltinTypes.BOOL, "X7");
    Variable X8 = Variable.create(BuiltinTypes.BOOL, "X8");
    Variable B = Variable.create(BuiltinTypes.BOOL, "B");
    Variable B2 = Variable.create(BuiltinTypes.BOOL, "B2");
    Variable B3 = Variable.create(BuiltinTypes.BOOL, "B3");
    Variable B4 = Variable.create(BuiltinTypes.BOOL, "B4");
    Variable B5 = Variable.create(BuiltinTypes.BOOL, "B5");
    Variable LetX1 = Variable.create(BuiltinTypes.BOOL, "LetX1");
    Variable LetX2 = Variable.create(BuiltinTypes.BOOL, "?LetX2");
    Variable LetX3 = Variable.create(BuiltinTypes.BOOL, "?LetX1");
    Variable LetX4 = Variable.create(BuiltinTypes.BOOL, "$xLetX1");
    Variable LetX5 = Variable.create(BuiltinTypes.BOOL, "$xLetX5");

    IfThenElse ite = IfThenElse.create(B, X1, X);
    IfThenElse ite2 = IfThenElse.create(B2, X1, LetX1);
    IfThenElse ite3 = IfThenElse.create(B3, X2, X3);
    IfThenElse ite4 = IfThenElse.create(B4, X4, LetX2);
    LetExpression let1 = LetExpression
        .create(LetX4, PropositionalCompound.create(LetX3, AND, LetX5), LetX4);
    LetExpression let2 = LetExpression.create(LetX3, ite4, let1);
    LetExpression let3 = LetExpression.create(LetX2, ite3, let2);
    LetExpression let4 = LetExpression.create(LetX5, ite2, let3);
    LetExpression let5 = LetExpression.create(LetX1, ite, let4);

    Expression flat = let5.flattenLetExpression();
    Set<Variable<?>> vars = ExpressionUtil.freeVariables(flat);
    assertFalse(vars.contains(LetX1));
    assertFalse(vars.contains(LetX2));
    assertFalse(vars.contains(LetX3));
    assertFalse(vars.contains(LetX4));
    assertFalse(vars.contains(LetX5));
  }


  public class DummyVisitorForTest extends AbstractExpressionVisitor<Expression, Boolean> {

    @Override
    protected Expression defaultVisit(Expression expression, Boolean data) {
      return expression;
    }
  }
}
