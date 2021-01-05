/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377
 * the original license is:
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
 *
 * Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues
 * under Apache 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.simplifiers;

import static org.testng.Assert.assertEquals;
import static org.testng.AssertJUnit.assertFalse;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.math.BigInteger;
import java.util.Set;
import org.testng.annotations.Test;

public class ReplaceArithmeticExpressionTest {
  private Expression x = Variable.create(BuiltinTypes.SINT32, "x");
  private Expression x1 = Variable.create(BuiltinTypes.SINT32, "x1");

  private Expression c1 = Constant.create(BuiltinTypes.SINT32, 1);
  private Expression c2 = Constant.create(BuiltinTypes.SINT32, 2);
  private Expression c5 = Constant.create(BuiltinTypes.SINT32, 5);
  private Expression xInit = NumericBooleanExpression.create(x, NumericComparator.LT, c2);

  private Expression update =
      NumericBooleanExpression.create(
          x1, NumericComparator.EQ, NumericCompound.create(x, NumericOperator.PLUS, c1));
  private Expression guardCheck = NumericBooleanExpression.create(x1, NumericComparator.LT, c5);
  private Expression completeUpdate = ExpressionUtil.and(xInit, update, guardCheck);

  private Expression guardReplaced =
      NumericBooleanExpression.create(
          NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.LT, c5);
  private Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
  private Constant c4 = Constant.create(BuiltinTypes.SINT32, 20);

  private Expression furtherUpdate = NumericBooleanExpression.create(x2, NumericComparator.EQ, x1);
  private Expression checkOnX2 = NumericBooleanExpression.create(x2, NumericComparator.GE, c4);
  private Expression all = ExpressionUtil.and(completeUpdate, furtherUpdate, checkOnX2);

  private Expression x2GuardReplacement =
      NumericBooleanExpression.create(
          NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.GE, c4);

  @Test(groups = {"simplifiers", "base"})
  public void simpleReplacementTest() {
    Expression expected = ExpressionUtil.and(xInit, guardReplaced);

    assertEquals(NumericSimplificationUtil.simplify(completeUpdate), expected);
  }

  @Test(groups = {"simplifiers", "base"})
  public void noReplacementTest() {
    Expression anotherAssignment = NumericBooleanExpression.create(x1, NumericComparator.EQ, c5);
    Expression expected = ExpressionUtil.and(completeUpdate, anotherAssignment);
    assertEquals(NumericSimplificationUtil.simplify(expected), expected);
  }

  @Test(groups = {"simplifiers", "base"})
  public void replacementInChainTest() {
    Expression expected = ExpressionUtil.and(xInit, guardReplaced, x2GuardReplacement);
    assertEquals(NumericSimplificationUtil.simplify(all), expected);
  }

  @Test(groups = {"simplifiers", "base"})
  public void replacementInManipulatedChainTest() {
    Variable x3 = Variable.create(BuiltinTypes.SINT32, "x3");
    Expression extension =
        NumericBooleanExpression.create(
            x3, NumericComparator.EQ, NumericCompound.create(x2, NumericOperator.PLUS, c5));

    Expression checkX3 = NumericBooleanExpression.create(x3, NumericComparator.LT, c4);
    Expression toSimplify = ExpressionUtil.and(all, checkX3, extension);
    Expression simplified = NumericSimplificationUtil.simplify(toSimplify);

    Set<Variable<?>> variables = ExpressionUtil.freeVariables(simplified);

    assertFalse(variables.contains(x2));
    assertFalse(variables.contains(x1));
    assertFalse(variables.contains(x3));
  }

  @Test(groups = {"simplifiers", "base"})
  public void replacementWithNotInExpression() {
    /*
     * Is it always allowed to convert a not (a == b) into (a != b)?
     * This might simplify the implementation of this test case further.
     * TODO: Investigate negation push into the theory.
     */
    Constant c0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0));
    Constant c4 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(4));
    Constant c5 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(5));
    Constant c12 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(12));
    Constant c42 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(42));
    Variable y1 = Variable.create(BuiltinTypes.INTEGER, "y1");
    Variable x1 = Variable.create(BuiltinTypes.INTEGER, "x1");
    Variable y2 = Variable.create(BuiltinTypes.INTEGER, "y2");
    Variable x2 = Variable.create(BuiltinTypes.INTEGER, "x2");

    Expression exprEQ = NumericBooleanExpression.create(y1, NumericComparator.EQ, c5);
    Expression lt = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);
    Expression negatedEQ =
        Negation.create(NumericBooleanExpression.create(x1, NumericComparator.EQ, c42));

    Expression exprEQ2 = NumericBooleanExpression.create(x2, NumericComparator.EQ, c4);
    Expression exprEQ3 = NumericBooleanExpression.create(y2, NumericComparator.EQ, c12);

    Expression problem = ExpressionUtil.and(exprEQ, lt, negatedEQ, exprEQ2, exprEQ3);

    Expression res = NumericSimplificationUtil.simplify(problem);
    assertEquals(res, PropositionalCompound.create(lt, LogicalOperator.AND, negatedEQ));
  }
}
