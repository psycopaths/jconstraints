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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import org.smtlib.IParser;
import org.smtlib.IParser.ParserException;
import org.testng.annotations.Test;

public class LetExpressionParsingTest {
  @Test(groups = {"jsmtlib", "base"})
  public void simpleLetExampleTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final String input =
        "(declare-fun x () Int)\n"
            + "(declare-fun y () Int)\n"
            + "(declare-fun m () Bool)\n"
            + "(declare-fun n () Bool)\n"
            + "(declare-fun z () Int)\n"
            + "(assert (= m (let ((a (= z (+ x 5))) (b (= y (* x 2))) (c (= x 0))) (and a b c (<="
            + " y 10)))))\n"
            + "(assert (= n (and (= z (+ x 5)) (= y (* x 2)) (= x 0) (<= y 10))))\n"
            + "(assert (= m n))\n"
            + "(check-sat)\n";

    final SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    assertEquals(problem.variables.size(), 5);
    assertEquals(problem.assertions.size(), 3);

    for (final Variable var : problem.variables) {
      if (var.getName().equals("x") || var.getName().equals("y") || var.getName().equals("z")) {
        assertEquals(var.getType(), BuiltinTypes.INTEGER);
      } else {
        assertEquals(var.getType(), BuiltinTypes.BOOL);
      }
    }

    final Expression assertion1 = problem.assertions.get(0);
    assertEquals(assertion1.getClass(), PropositionalCompound.class);
    final PropositionalCompound cAssertion1 = (PropositionalCompound) assertion1;
    assertEquals(cAssertion1.getRight().getClass(), LetExpression.class);
    final LetExpression letExpr = (LetExpression) cAssertion1.getRight();
    assertEquals(letExpr.getParameters().size(), 3);
    assertEquals(letExpr.getMainValue().getClass(), PropositionalCompound.class);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void nestedLetExampleTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final String input =
        "(declare-fun x () Int)\n"
            + "(declare-fun y () Int) \n"
            + "(declare-fun m () Bool) \n"
            + "(declare-fun n () Bool) \n"
            + "(declare-fun z () Int) \n"
            + " (assert (= m (let ((a (= z (+ x 5)))) (let ((b (= y (* x 2))) (c (= x 0))) (and a"
            + " b c (<= y 10))))))\n"
            + "(assert (= n (and (= z (+ x 5)) (= y (* x 2)) (= x 0) (<= y 10))))\n"
            + "(assert (= m n)) \n"
            + " (check-sat)";

    final Set<String> names = new HashSet<>();
    names.add("x");
    names.add("y");
    names.add("m");
    names.add("n");
    names.add("z");

    final SMTProblem problem = SMTLIBParser.parseSMTProgram(input);

    for (final Variable v : problem.variables) {
      assertTrue(names.contains(v.getName()), v.getName() + " not in names: " + names);
    }
  }

  @Test(groups = {"jsmtlib", "base"})
  public void underscoresInNameTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final String input =
        "(declare-fun x_1 () Real)\n"
            + "(declare-fun x_1_2 () Real)\n"
            + "(declare-fun abc_1_xyz () Real)\n"
            + "(declare-fun x_2 () Real)\n"
            + "(assert (> x_1_2 (* x_1 x_2)))";

    final Set<String> names = new HashSet<>();
    names.add("x_1");
    names.add("x_1_2");
    names.add("abc_1_xyz");
    names.add("x_2");

    final SMTProblem problem = SMTLIBParser.parseSMTProgram(input);

    for (final Variable v : problem.variables) {
      assertTrue(names.contains(v.getName()), v.getName() + " not in names: " + names);
    }
    assertEquals(problem.assertions.get(0).getType(), BuiltinTypes.BOOL);
  }

  @Test(groups = {"jsmtlib"})
  public void parse_constraint_1635444()
      throws SMTLIBParserException, ParserException, IOException {
    final SMTProblem problem = parseResourceFile("constraint-1635444.txt");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), LetExpression.class);
  }
}
