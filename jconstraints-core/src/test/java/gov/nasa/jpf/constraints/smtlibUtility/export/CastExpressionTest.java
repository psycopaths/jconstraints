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

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class CastExpressionTest {
  SolverContext se;
  ByteArrayOutputStream baos;
  PrintStream ps;

  @BeforeMethod(alwaysRun = true)
  public void initialize() {
    baos = new ByteArrayOutputStream();
    ps = new PrintStream(baos);
    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
  }

  @Test(groups = {"base", "smt-export"})
  public void castSINT32IntegerTest() {
    String expected =
        "(declare-const X (_ BitVec 32))\n"
            + "(assert (ite (bvslt X #x00000000) (- (bv2nat X)) (bv2nat X)))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT32, "X"), BuiltinTypes.INTEGER);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void castIntegerSINT32Test() {
    String expected = "(declare-const X Int)\n" + "(assert ((_ int2bv 32) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.INTEGER, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void castIntegerSINT8Test() {
    String expected = "(declare-const X Int)\n(assert ((_ int2bv 8) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.INTEGER, "X"), BuiltinTypes.SINT8);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void castSINT8SINT32Test() {
    String expected = "(declare-const X (_ BitVec 8))\n(assert ((_ sign_extend 24) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT8, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void castSINT8UINT16Test() {
    String expected = "(declare-const X (_ BitVec 8))\n(assert ((_ sign_extend 8) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT8, "X"), BuiltinTypes.UINT16);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void castUINT16SINT32Test() {
    String expected = "(declare-const X (_ BitVec 16))\n(assert ((_ zero_extend 16) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.UINT16, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }
}
