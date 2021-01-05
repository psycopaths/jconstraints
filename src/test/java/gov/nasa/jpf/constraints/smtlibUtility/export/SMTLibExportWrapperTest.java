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
package gov.nasa.jpf.constraints.smtlibUtility.export;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import org.junit.Assert;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class SMTLibExportWrapperTest {

  @Test(groups = {"jsmtlib", "base"})
  public void testSMTLibExport() {

    DontKnowSolver back = new DontKnowSolver();
    SMTLibExportWrapper se = new SMTLibExportWrapper(back, System.out);

    Variable x = new Variable(BuiltinTypes.BOOL, "x");
    Variable y = new Variable(BuiltinTypes.SINT32, "y");
    Constant c = new Constant(BuiltinTypes.SINT32, 3);

    IfThenElse ite =
        new IfThenElse(
            x,
            new NumericCompound<>(y, NumericOperator.PLUS, c),
            new NumericCompound<>(y, NumericOperator.MINUS, c));

    Expression<Boolean> expr = new NumericBooleanExpression(y, NumericComparator.GT, ite);
    se.isSatisfiable(expr);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void testSMTLibStringExport()
      throws IOException, SMTLIBParserException, IParser.ParserException {
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun PCTEMP_LHS_1 () Bool)\n"
                + "(declare-fun PCTEMP_LHS_3 () String)\n"
                + "(declare-fun PCTEMP_LHS_4_idx_0 () String)\n"
                + "(declare-fun PCTEMP_LHS_5 () String)\n"
                + "(declare-fun T0_24 () String)\n"
                + "(declare-fun T_12 () Bool)\n"
                + "(declare-fun T_13 () Bool)\n"
                + "(declare-fun T_14 () Bool)\n"
                + "(declare-fun T_15 () Bool)\n"
                + "(declare-fun T_16 () Bool)\n"
                + "(declare-fun T_17 () Bool)\n"
                + "(declare-fun T_18 () Bool)\n"
                + "(declare-fun T_19 () Bool)\n"
                + "(declare-fun T_1a () Bool)\n"
                + "(declare-fun T_1b () Bool)\n"
                + "(declare-fun T_1c () Bool)\n"
                + "(declare-fun T_2 () Bool)\n"
                + "(declare-fun T_3 () Int)\n"
                + "(declare-fun T_4 () Int)\n"
                + "(declare-fun T_6 () Int)\n"
                + "(declare-fun T_7 () Bool)\n"
                + "(declare-fun T_8 () Bool)\n"
                + "(declare-fun T_9 () Int)\n"
                + "(declare-fun T_a () Bool)\n"
                + "(declare-fun T_b () Bool)\n"
                + "(declare-fun T_c () Int)\n"
                + "(declare-fun T_d () Bool)\n"
                + "(declare-fun T_e () Bool)\n"
                + "(declare-fun var_0xINPUT_39034 () String)\n"
                + "(assert (= T_2 (not PCTEMP_LHS_1)))\n"
                + "(assert T_2)\n"
                + "(assert (= T_3 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_4 (div T_3 10)))\n"
                + "(assert (= T_6 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_7 (< 70 T_6)))\n"
                + "(assert (= T_8 (not T_7)))\n"
                + "(assert T_8)\n"
                + "(assert (= T_9 (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_a (< 70 T_9)))\n"
                + "(assert (= T_b (not T_a)))\n"
                + "(assert T_b)\n"
                + "(assert (= T_c (str.len var_0xINPUT_39034)))\n"
                + "(assert (= T_d (< 70 T_c)))\n"
                + "(assert (= T_e (not T_d)))\n"
                + "(assert T_e)\n"
                + "(assert (= PCTEMP_LHS_3 var_0xINPUT_39034))\n"
                + "(assert (= T0_24 PCTEMP_LHS_4_idx_0))\n"
                + "(assert (= T0_24 PCTEMP_LHS_3))\n"
                + "(assert (= T_12 (= PCTEMP_LHS_5 \"[object\")))\n"
                + "(assert (= T_13 (not T_12)))\n"
                + "(assert T_13)\n"
                + "(assert (= T_15 (not T_14)))\n"
                + "(assert T_15)\n"
                + "(assert (= T_17 (not T_16)))\n"
                + "(assert T_17)\n"
                + "(assert (= T_19 (not T_18)))\n"
                + "(assert T_19)\n"
                + "(assert (= T_1b (not T_1a)))\n"
                + "(assert T_1b)\n"
                + "(assert T_1c)\n"
                + "(check-sat)");

    DontKnowSolver back = new DontKnowSolver();
    SMTLibExportWrapper se = new SMTLibExportWrapper(back, System.out);
    SolverContext ctx = se.createContext();

    ctx.push();
    for (Expression<Boolean> e : problem.assertions) {
      // System.out.println("; " + e);
      ctx.add(e);
    }

    ConstraintSolver.Result res = ctx.isSatisfiable();
    Assert.assertEquals(ConstraintSolver.Result.DONT_KNOW, res);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void testSMTLibLetExport() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    Constant c = Constant.create(BuiltinTypes.SINT32, 5);
    Expression<Boolean> expr = NumericBooleanExpression.create(x, NumericComparator.GT, c);
    Constant c4 = Constant.create(BuiltinTypes.SINT32, 4);
    LetExpression letExpr = LetExpression.create(x, c4, expr);

    DontKnowSolver back = new DontKnowSolver();
    SMTLibExportWrapper se = new SMTLibExportWrapper(back, System.out);
    SolverContext ctx = se.createContext();

    ctx.push();
    ctx.isSatisfiable(letExpr);
  }
}
