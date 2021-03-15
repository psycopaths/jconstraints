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

package gov.nasa.jpf.constraints.smtlib;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.testng.annotations.Test;

public class QfLiaTest {
  @Test
  public void Problem2Test() throws IOException, SMTLIBParserException, URISyntaxException {
    URL smtFile = QfLiaTest.class.getClassLoader().getResource("problem_2__008.smt2");
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            Files.readAllLines(Paths.get(smtFile.toURI())).stream()
                .reduce(
                    "",
                    (a, b) -> {
                      return b.startsWith(";") ? a : a + b;
                    }));

    NativeZ3Solver z3 = new NativeZ3Solver();
    Valuation model = new Valuation();
    ConstraintSolver.Result jRes = z3.solve(problem.getAllAssertionsAsConjunction(), model);
    assertEquals(jRes, ConstraintSolver.Result.SAT);
    assertTrue(problem.getAllAssertionsAsConjunction().evaluate(model));
  }
}
