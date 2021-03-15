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

package io.github.tudoaqua.jconstraints.cvc4.expressions;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc4.AbstractCVC4Test;
import org.testng.annotations.Test;

public class NumericTest extends AbstractCVC4Test {

  @Test
  public void firstTest() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    Constant c4 = Constant.create(BuiltinTypes.SINT32, 5);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.LT, c4);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));

    expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

    val = new Valuation();
    res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void secondTest() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    NumericCompound computation1 =
        NumericCompound.create(x, NumericOperator.MUL, Constant.create(BuiltinTypes.SINT32, 2));
    computation1 =
        NumericCompound.create(
            computation1, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 1));
    CastExpression casted = CastExpression.create(computation1, BuiltinTypes.UINT16);
    casted = CastExpression.create(casted, BuiltinTypes.SINT32);
    BitvectorExpression bvOr =
        BitvectorExpression.create(
            casted, BitvectorOperator.OR, Constant.create(BuiltinTypes.SINT32, 2));
    BitvectorExpression bvAnd =
        BitvectorExpression.create(
            bvOr, BitvectorOperator.AND, Constant.create(BuiltinTypes.SINT32, 3));
    NumericBooleanExpression compare =
        NumericBooleanExpression.create(
            bvAnd, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(compare, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(compare.evaluate(val));
  }

  @Test
  public void misc1Test() {
    // (-((3 * (('_int0' % 10) + 0))) <= (3 * (('_int0' % 10) + 0)))
    Variable x = Variable.create(BuiltinTypes.SINT32, "_int0");
    Expression reminder =
        NumericCompound.create(x, NumericOperator.REM, Constant.create(BuiltinTypes.SINT32, 10));
    Expression addition =
        NumericCompound.create(
            reminder, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 0));
    Expression multiplication =
        NumericCompound.create(
            Constant.create(BuiltinTypes.SINT32, 3), NumericOperator.MUL, addition);
    Expression unary = UnaryMinus.create(multiplication);
    NumericBooleanExpression lt =
        NumericBooleanExpression.create(unary, NumericComparator.LE, multiplication);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(lt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(lt.evaluate(val));
  }
}
