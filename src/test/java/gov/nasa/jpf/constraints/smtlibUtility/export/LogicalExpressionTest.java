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
package gov.nasa.jpf.constraints.smtlibUtility.export;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.OR;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.XOR;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class LogicalExpressionTest {
  Variable var1, var2;

  SolverContext se;
  ByteArrayOutputStream baos;
  PrintStream ps;

  @BeforeMethod(alwaysRun = true)
  public void initialize() {
    var1 = Variable.create(BuiltinTypes.BOOL, "x");
    var2 = Variable.create(BuiltinTypes.BOOL, "y");
    baos = new ByteArrayOutputStream();
    ps = new PrintStream(baos);
    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
  }

  @Test(groups = {"base", "smt-export"})
  public void PropositionalCompoundAndTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (and x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, AND, var2);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void PropositionalCompoundOrTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (or x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, OR, var2);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void PropositionalCompoundImplyTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (=> x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, IMPLY, var2);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void PropositionalCompoundEquivalentTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (= x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, EQUIV, var2);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void PropositionalXORAndTest() {
    String expected =
        "(declare-const x Bool)\n" + "(declare-const y Bool)\n" + "(assert (xor x y))\n";
    PropositionalCompound expr = PropositionalCompound.create(var1, XOR, var2);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void NegationTest() {
    String expected = "(declare-const x Bool)\n" + "(assert (not x))\n";
    Negation expr = Negation.create(var1);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void ifThenElseTest() {
    String expected =
        "(declare-const x Bool)\n"
            + "(declare-const y Bool)\n"
            + "(declare-const z Bool)\n"
            + "(assert (ite x y z))"
            + "\n";

    Variable var1 = Variable.create(BuiltinTypes.BOOL, "x");
    Variable var2 = Variable.create(BuiltinTypes.BOOL, "y");
    Variable var3 = Variable.create(BuiltinTypes.BOOL, "z");
    IfThenElse expr = IfThenElse.create(var1, var2, var3);
    se.add(expr);
    assertEquals(baos.toString(), expected);
  }
}
