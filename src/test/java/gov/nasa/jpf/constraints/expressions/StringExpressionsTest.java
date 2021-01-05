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
package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

public class StringExpressionsTest {

  @Test(groups = {"basic", "string-expressions"})
  public void toLowerEvaluationTest() {
    Variable var = Variable.create(BuiltinTypes.STRING, "x");
    Constant cU = Constant.create(BuiltinTypes.STRING, "UpperCase");
    Constant target = Constant.create(BuiltinTypes.STRING, "uppercase");

    StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
    StringCompoundExpression upper = StringCompoundExpression.createToLower(var);
    StringBooleanExpression part2 = StringBooleanExpression.createEquals(upper, target);
    PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);

    Valuation val = new Valuation();
    val.setValue(var, "UpperCase");
    assertTrue(complete.evaluate(val));

    val.setValue(var, "upperCase");
    assertFalse(complete.evaluate(val));
  }

  @Test(groups = {"basic", "string-expressions"})
  public void toAndFromIntEvaluationTest() {
    Variable x = Variable.create(BuiltinTypes.STRING, "x");
    Constant c = Constant.create(BuiltinTypes.STRING, "C");
    Expression toInt = StringIntegerExpression.createToInt(x);
    Expression fromInt = StringCompoundExpression.createToString(toInt);
    StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, x);

    Valuation val = new Valuation();
    val.setValue(x, "10");
    assertTrue(equals.evaluate(val));
  }

  @Test(groups = {"basic", "string-expressions"})
  public void equalsTestSpecialChars() {
    Variable x = Variable.create(BuiltinTypes.STRING, "_string1");
    Constant c = Constant.create(BuiltinTypes.STRING, "W\f49-44-44");
    StringBooleanExpression equals = StringBooleanExpression.createEquals(x, c);

    Valuation val = new Valuation();
    val.setValue(x, "W\f49-44-44");

    assertTrue(equals.evaluate(val));
  }
}
