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
package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.math.BigInteger;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class SMTLIBParserTest {

  @Test
  public void parsingRoundTripPrimeConesTest()
      throws IOException, SMTLIBParserException, IParser.ParserException {
    final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_sat_15.smt2");

    assertEquals(
        problem.variables.size(),
        15,
        "There are 15 variables declared in the original SMT-Problem,"
            + "hence 15 variables are expected in the parsed problem");
    for (final Variable v : problem.variables) {
      assertEquals(
          v.getType(),
          BuiltinTypes.INTEGER,
          "They are declared as Int in the SMT-problem,"
              + "which is in jConstraint represented as Integer.");
    }
    assertEquals(problem.assertions.size(), 31, "There are 31 assertions in the original problem.");

    final Expression assertion1 = problem.assertions.get(0);
    assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression convertedAssertion1 = (NumericBooleanExpression) assertion1;
    assertEquals(convertedAssertion1.getLeft().getClass(), Variable.class);
    final Variable left = (Variable) convertedAssertion1.getLeft();
    assertEquals(left.getName(), "x_0");
    assertEquals(convertedAssertion1.getRight().toString(), "0");
    assertEquals(((NumericBooleanExpression) assertion1).getComparator(), NumericComparator.GE);

    final Expression assertion30 = problem.assertions.get(29);
    assertEquals(assertion30.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression convertedAssertion30 = (NumericBooleanExpression) assertion30;
    assertEquals(convertedAssertion30.getLeft().getClass(), NumericCompound.class);
    final NumericCompound leftPart = (NumericCompound) convertedAssertion30.getLeft();
    assertEquals(leftPart.getRight().getClass(), NumericCompound.class);
    final NumericCompound testTarget = (NumericCompound) leftPart.getRight();
    assertEquals(testTarget.getRight().getClass(), Variable.class);
    final Variable x14 = (Variable) testTarget.getRight();
    assertEquals(x14.getName(), "x_14");
    assertEquals(testTarget.getLeft().getClass(), UnaryMinus.class);
    final UnaryMinus leftTarget = (UnaryMinus) testTarget.getLeft();
    assertEquals(leftTarget.getNegated().getClass(), Constant.class);
    final Constant v282 = (Constant) leftTarget.getNegated();
    assertEquals(v282.getValue(), BigInteger.valueOf(282));
  }

  // This test is used for driving the development and the next, that should be enabled an make
  // pass.
  @Test(enabled = false)
  public void parsingRoundTripPRP718Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/prp-7-18.smt2");

    assertEquals(problem.variables.size(), 17);
    assertEquals(problem.assertions.size(), 1);
  }
}
