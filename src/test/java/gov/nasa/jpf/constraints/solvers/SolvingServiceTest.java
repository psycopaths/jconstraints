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
package gov.nasa.jpf.constraints.solvers;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import org.smtlib.IParser;
import org.testng.annotations.Test;

/*
 * All test cases in this class are supposed to be executed for testing
 * avilability of solvers. As this test can not be run by jConstraints
 * alone, they are in a special test group.
 * @TODO: make a build target for running this kind of tests.
 *
 * @author: Malte Mues (@mmuesly)
 */

public class SolvingServiceTest {

  @Test(groups = {"testSolver"})
  public void atLeastZ3available() {
    final SolvingService service = new SolvingService();
    System.out.println(service.supportedSolvers);
    assert (service.supportedSolvers.contains("Z3")
        || service.supportedSolvers.contains("NativeZ3"));
  }

  @Test(groups = {"testSolver"})
  public void simpleSolving() {
    final SolvingService service = new SolvingService();
    final Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    final Variable y = Variable.create(BuiltinTypes.SINT32, "y");
    final Constant c0 = Constant.create(BuiltinTypes.SINT32, 10);
    final Constant c1 = Constant.create(BuiltinTypes.SINT32, 3);

    final NumericBooleanExpression expr1 =
        NumericBooleanExpression.create(x, NumericComparator.EQ, c0);
    final NumericBooleanExpression expr2 =
        NumericBooleanExpression.create(y, NumericComparator.EQ, x);
    final NumericBooleanExpression expr3 =
        NumericBooleanExpression.create(y, NumericComparator.LE, c1);

    final ConstraintSolver.Result res =
        service.solve(ExpressionUtil.and(expr1, expr2, expr3), null);
    assertEquals(res, ConstraintSolver.Result.UNSAT);
  }

  @Test(groups = {"testSolver"})
  public void solveSMTProblemSATTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_sat_15.smt2");

    final SolvingService service = new SolvingService();
    final Result res = service.solve(problem);
    assertEquals(res, Result.SAT);
  }

  @Test(groups = {"testSolver"})
  public void solveSMTProblemUNSATTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_unsat_10.smt2");

    final SolvingService service = new SolvingService();
    final Result res = service.solve(problem);
    assertEquals(res, Result.UNSAT);
  }

  @Test(groups = {"testSolver"})
  public void solveGen09Test() throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/gen-09.smt2");

    final SolvingService service = new SolvingService();
    final Result res = service.solve(problem);
    assertEquals(res, Result.SAT);
  }
}
