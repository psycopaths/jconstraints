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

package io.github.tudoaqua.jconstraints.cvc4.smtlibBenchmarks;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import io.github.tudoaqua.jconstraints.cvc4.AbstractCVC4Test;
import java.io.IOException;
import java.net.URISyntaxException;
import org.testng.annotations.Test;

public class QF_LIA_RoundTripTest extends AbstractCVC4Test {

  @Test
  public void Problem2Test() throws IOException, SMTLIBParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("problem_2__008.smt2");
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    cvc4Context.add(expr);
    ConstraintSolver.Result jRes = cvc4Context.solve(model);
    assertEquals(jRes, ConstraintSolver.Result.SAT);
    assertTrue(problem.getAllAssertionsAsConjunction().evaluate(model));
  }
}
