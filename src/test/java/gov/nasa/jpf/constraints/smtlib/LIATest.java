/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * <p>Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p> Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com)
 * We license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.smtlib;

import static org.testng.AssertJUnit.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import java.net.URISyntaxException;
import org.smtlib.IParser.ParserException;
import org.testng.annotations.Test;

public class LIATest {

  @Test
  public void LIAPsyco014Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("psyco/014.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    //assertEquals(2, problem.assertions.size());
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.println(expr.toString());

    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.UNSAT, jRes);
  }

  @Test
  public void LIAPsyco070Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("psyco/070.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(jRes, ConstraintSolver.Result.UNSAT);
  }

  @Test
  public void LIAPsyco160Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("psyco/160.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.UNSAT, jRes);
  }

  @Test
  public void LIAPsyco167Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("psyco/167.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.UNSAT, jRes);
  }

  @Test
  public void LIAPsyco170Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("psyco/170.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
  }

  @Test
  public void automizer01Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("Problem15_label00_false-unreach-call.c_5.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(Result.UNSAT, jRes);
  }

  @Test
  public void automizer02Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("Problem18_label34_false-unreach-call.c_10.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(Result.SAT, jRes);
  }

  @Test(enabled = false)
  public void automizer03Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("Problem18_label34_false-unreach-call.c_12.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(Result.SAT, jRes);
  }

  @Test
  public void tptp01Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("NUM916_1.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(Result.UNSAT, jRes);
  }

  @Test
  public void tptp02Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("ARI5901.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(Result.UNSAT, jRes);
  }
}
