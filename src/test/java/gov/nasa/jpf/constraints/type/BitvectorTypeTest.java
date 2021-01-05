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
package gov.nasa.jpf.constraints.type;

import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

public class BitvectorTypeTest {

  @Test(groups = {"basic", "types"})
  public void firstTest() throws ImpreciseRepresentationException {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    NumericCompound computation1 =
        NumericCompound.create(x, NumericOperator.MUL, Constant.create(BuiltinTypes.SINT32, 2));
    computation1 =
        NumericCompound.create(
            computation1, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 1));
    CastExpression casted = CastExpression.create(computation1, BuiltinTypes.UINT16);
    casted = CastExpression.create(casted, BuiltinTypes.SINT32);
    BitvectorExpression bvOr =
        BitvectorExpression.create(
            casted, BitvectorOperator.OR, Constant.create(BuiltinTypes.SINT32, 2));
    BitvectorExpression bvAnd =
        BitvectorExpression.create(
            bvOr, BitvectorOperator.AND, Constant.create(BuiltinTypes.SINT32, 3));
    NumericBooleanExpression compare =
        NumericBooleanExpression.create(
            bvAnd, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3));

    Valuation val = new Valuation();
    val.setParsedValue(x, "3");
    assertTrue(compare.evaluate(val));
  }
}
