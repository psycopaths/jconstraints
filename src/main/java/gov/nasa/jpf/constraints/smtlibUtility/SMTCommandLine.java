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
package gov.nasa.jpf.constraints.smtlibUtility;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import org.smtlib.IParser;

public class SMTCommandLine {

  public static void main(String args[])
      throws IOException, SMTLIBParserException, IParser.ParserException {
    if (args.length == 1) {
      String filename = args[0];
      System.out.println("Trying to parse filename: " + filename);

      try (BufferedReader reader = new BufferedReader(new FileReader(filename))) {
        String smtProgram = reader.lines().reduce((a, b) -> b.startsWith(";") ? a : a + b).get();
        SMTProblem problem = SMTLIBParser.parseSMTProgram(smtProgram);

        ConstraintSolverFactory factory = ConstraintSolverFactory.getRootFactory();
        ConstraintSolver solver = factory.createSolver();
        ConstraintSolver.Result result =
            solver.isSatisfiable(problem.getAllAssertionsAsConjunction());
        System.out.println("The result ist: " + result.name());
      }
    } else {
      System.out.println("This script expects at least one filename to solve.");
    }
  }
}
