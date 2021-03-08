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

package gov.nasa.jpf.constraints.smtlibUtility.export;

import static gov.nasa.jpf.constraints.util.CharsetIO.toNormalizedStringUTF8;
import static gov.nasa.jpf.constraints.util.CharsetIO.wrapInUTF8PrintStream;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class BitvectorExpressionTest {
  Variable x;
  Constant c0SINT32;
  SolverContext se;

  ByteArrayOutputStream baos;
  PrintStream ps;

  @BeforeMethod(alwaysRun = true)
  public void initialize() {
    x = Variable.create(BuiltinTypes.SINT32, "X");
    c0SINT32 = Constant.create(BuiltinTypes.SINT32, 0);

    baos = new ByteArrayOutputStream();
    ps = wrapInUTF8PrintStream(baos);

    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
  }

  @Test(groups = {"base", "smt-export"})
  public void BVAndTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvand X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.AND, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVOrTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvor X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.OR, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVXorTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvxor X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.XOR, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVShiftLTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvshl X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTL, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVShiftRTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvashr X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTR, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVShiftURTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvlshr X #x00000000))\n";

    BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTUR, c0SINT32);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVNegationTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvnot X))\n";

    BitvectorNegation expr = BitvectorNegation.create(x);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void BVUnaryMinusTest() {
    String expected = "(declare-const X (_ BitVec 32))\n(assert (bvneg X))\n";

    UnaryMinus expr = UnaryMinus.create(x);
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }
}
