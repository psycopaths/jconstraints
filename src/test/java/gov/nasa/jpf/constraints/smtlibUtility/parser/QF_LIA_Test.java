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
package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.IOException;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class QF_LIA_Test {
  @Test(groups = {"jsmtlib", "base"})
  public void parsingLetAndIte_PRP_3_20_Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("QF_LIA/prp-3-20.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), LetExpression.class);
  }
}
