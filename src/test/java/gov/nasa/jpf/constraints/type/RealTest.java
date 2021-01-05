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
package gov.nasa.jpf.constraints.type;

import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.apache.commons.math3.fraction.BigFraction;
import org.testng.annotations.Test;

public class RealTest {

  @Test(groups = {"types", "base"})
  public void simpleRealTest() {
    Variable x = Variable.create(BuiltinTypes.REAL, "x");
    Constant c2_3 = Constant.create(BuiltinTypes.REAL, BigFraction.TWO_THIRDS);
    NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c2_3);
    Valuation valSat = new Valuation();
    valSat.setValue(x, BigFraction.TWO_THIRDS);

    Valuation valUnsat = new Valuation();
    valUnsat.setValue(x, BigFraction.FOUR_FIFTHS);

    assertTrue(expr.evaluate(valSat));
    assertFalse(expr.evaluate(valUnsat));
  }
}
