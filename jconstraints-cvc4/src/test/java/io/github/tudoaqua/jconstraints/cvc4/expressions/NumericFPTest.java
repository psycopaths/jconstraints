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

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.PLUS;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
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

public class NumericFPTest extends AbstractCVC4Test {

  @Test
  public void doubleComparisonTest() {
    Constant c0 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, GT, c0);
    NumericBooleanExpression expr2 = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
    assertFalse(expr2.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(expr2, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr2.evaluate(val));
    assertFalse(expr.evaluate(val));
  }

  @Test
  public void castDoubleTest() {
    Constant c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant c0 = Constant.createCasted(BuiltinTypes.SINT32, 0);
    Constant c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");

    NumericCompound doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT32), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castIntToDoubleTest() {
    Constant c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 1);
    Variable x1 = Variable.create(BuiltinTypes.SINT32, "x");

    NumericCompound plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.DOUBLE), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void GreateMaxIntHalfTest() {
    Constant c = Constant.create(BuiltinTypes.DOUBLE, (double) Integer.MAX_VALUE / 2);
    Variable x = Variable.create(BuiltinTypes.DOUBLE, "x");
    NumericBooleanExpression gt = NumericBooleanExpression.create(x, GT, c);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gt.evaluate(val));
  }

  @Test
  public void floatComparisonTest() {
    Constant c0 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, GT, c0);
    NumericBooleanExpression expr2 = NumericBooleanExpression.create(x1, NumericComparator.LT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
    assertFalse(expr2.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(expr2, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr2.evaluate(val));
    assertFalse(expr.evaluate(val));
  }

  @Test
  public void castFloatTest() {
    Constant c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant c0 = Constant.createCasted(BuiltinTypes.SINT32, 0);
    Constant c00 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");

    NumericCompound doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT32), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castIntToFloatTest() {
    Constant c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 1);
    Variable x1 = Variable.create(BuiltinTypes.SINT32, "x");

    NumericCompound plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.FLOAT), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void GreateMaxIntQuarterTest() {
    Constant c = Constant.create(BuiltinTypes.FLOAT, (float) Integer.MAX_VALUE / 4);
    Variable x = Variable.create(BuiltinTypes.FLOAT, "x");
    NumericBooleanExpression gt = NumericBooleanExpression.create(x, GT, c);
    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gt, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gt.evaluate(val));
  }

  @Test
  public void castLongToDoubleTest() {
    Constant c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant c1 = Constant.create(BuiltinTypes.SINT64, 1l);
    Variable x1 = Variable.create(BuiltinTypes.SINT64, "x");

    NumericCompound plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.DOUBLE), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void castDoubleToLongTest() {
    Constant c10 = Constant.create(BuiltinTypes.DOUBLE, 1.0);
    Constant c0 = Constant.create(BuiltinTypes.SINT64, 0l);
    Constant c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");

    NumericCompound doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT64), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void castLongToFloatTest() {
    Constant c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant c1 = Constant.create(BuiltinTypes.SINT64, 1l);
    Variable x1 = Variable.create(BuiltinTypes.SINT64, "x");

    NumericCompound plus = NumericCompound.create(x1, PLUS, c1);
    NumericBooleanExpression eqDouble =
        NumericBooleanExpression.create(CastExpression.create(plus, BuiltinTypes.FLOAT), EQ, c10);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(eqDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(eqDouble.evaluate(val));
  }

  @Test
  public void castFloatToLongTest() {
    Constant c10 = Constant.create(BuiltinTypes.FLOAT, 1.0f);
    Constant c0 = Constant.createCasted(BuiltinTypes.SINT64, 0l);
    Constant c00 = Constant.create(BuiltinTypes.FLOAT, 0.0f);
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");

    NumericCompound doublePlus = NumericCompound.create(x1, PLUS, c10);
    NumericBooleanExpression gtDouble = NumericBooleanExpression.create(doublePlus, GT, c00);
    NumericBooleanExpression gtSINT32 =
        NumericBooleanExpression.create(
            CastExpression.create(doublePlus, BuiltinTypes.SINT64), GT, c0);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(gtDouble, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtDouble.evaluate(val));

    val = new Valuation();
    res = cvc4.solve(gtSINT32, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(gtSINT32.evaluate(val));
  }

  @Test
  public void notEqualsTest() {
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Variable x2 = Variable.create(BuiltinTypes.DOUBLE, "y");
    NumericBooleanExpression neExpr = NumericBooleanExpression.create(x1, NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void castDoubleToFloatTest() {
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Variable x2 = Variable.create(BuiltinTypes.FLOAT, "y");
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(CastExpression.create(x1, BuiltinTypes.FLOAT), NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void castFloatToDoubleTest() {
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Variable x2 = Variable.create(BuiltinTypes.DOUBLE, "y");
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(CastExpression.create(x1, BuiltinTypes.DOUBLE), NE, x2);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void FlaotSubtest() {
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Constant c1 = Constant.create(BuiltinTypes.FLOAT, 119.0f);
    Constant c00 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
    NumericBooleanExpression neExpr =
        NumericBooleanExpression.create(
            CastExpression.create(
                NumericCompound.create(x1, NumericOperator.MINUS, c1), BuiltinTypes.DOUBLE),
            EQ,
            c00);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(neExpr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(neExpr.evaluate(val));
  }

  @Test
  public void floatConstTest() {
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Constant c1 = Constant.create(BuiltinTypes.FLOAT, 119.0f);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, EQ, c1);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void doubleConstTest() {
    Variable x1 = Variable.create(BuiltinTypes.DOUBLE, "x");
    Constant c1 = Constant.create(BuiltinTypes.DOUBLE, 119.0);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x1, EQ, c1);

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void floatEqualsTest() {
    Variable x1 = Variable.create(BuiltinTypes.FLOAT, "x");
    Variable c1 = Variable.create(BuiltinTypes.FLOAT, "y");
    NumericBooleanExpression expr =
        NumericBooleanExpression.create(x1, EQ, NumericCompound.create(x1, PLUS, c1));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(expr, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(expr.evaluate(val));
  }

  @Test
  public void unaryMinusTest() {
    Variable var = Variable.create(BuiltinTypes.FLOAT, "x");
    UnaryMinus um = UnaryMinus.create(var);
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(um, GT, Constant.create(BuiltinTypes.FLOAT, 5.0f));

    Valuation val = new Valuation();
    ConstraintSolver.Result res = cvc4.solve(nbe, val);
    assertEquals(res, ConstraintSolver.Result.SAT);
    assertTrue(nbe.evaluate(val));
  }
}
