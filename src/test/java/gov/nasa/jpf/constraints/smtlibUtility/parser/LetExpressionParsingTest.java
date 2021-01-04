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

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class LetExpressionParsingTest {
  @Test
  public void simpleLetExampleTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final String input =
        "(declare-fun x () Int)\n"
            + "(declare-fun y () Int)\n"
            + "(declare-fun m () Bool)\n"
            + "(declare-fun n () Bool)\n"
            + "(declare-fun z () Int)\n"
            + "(assert (= m (let ((a (= z (+ x 5))) (b (= y (* x 2))) (c (= x 0))) (and a b c (<= y "
            + "10)))))"
            + "\n"
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
    assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression cAssertion1 = (NumericBooleanExpression) assertion1;
    assertEquals(cAssertion1.getRight().getClass(), LetExpression.class);
    final LetExpression letExpr = (LetExpression) cAssertion1.getRight();
    assertEquals(letExpr.getParameters().size(), 3);
    assertEquals(letExpr.getMainValue().getClass(), PropositionalCompound.class);
  }

  @Test
  public void nestedLetExampleTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final String input =
        "(declare-fun x () Int)\n"
            + "(declare-fun y () Int) \n"
            + "(declare-fun m () Bool) \n"
            + "(declare-fun n () Bool) \n"
            + "(declare-fun z () Int) \n"
            + " (assert (= m (let ((a (= z (+ x 5)))) (let ((b (= y (* x 2))) (c (= x 0))) (and a b c "
            + "(<= y "
            + "10))))))\n"
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

  @Test
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
}
