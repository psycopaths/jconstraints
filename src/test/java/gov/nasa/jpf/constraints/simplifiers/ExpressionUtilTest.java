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
package gov.nasa.jpf.constraints.simplifiers;

import static org.testng.AssertJUnit.assertFalse;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

public class ExpressionUtilTest {

  @Test
  public void mustReplaceEveryVariableTest() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");

    Constant c20 = Constant.create(BuiltinTypes.SINT32, 20);

    Variable x1 = Variable.create(BuiltinTypes.SINT32, "x1");
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 1);

    Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
    Constant c0 = Constant.create(BuiltinTypes.SINT32, 0);

    Expression lessThan20 = NumericBooleanExpression.create(x, NumericComparator.LE, c20);
    Expression updatex1 =
        NumericBooleanExpression.create(
            x1, NumericComparator.EQ, NumericCompound.create(x, NumericOperator.PLUS, c1));
    Expression x1LessThan20 = NumericBooleanExpression.create(x1, NumericComparator.LE, c20);
    Expression updatex2 =
        NumericBooleanExpression.create(
            x2, NumericComparator.EQ, NumericCompound.create(x1, NumericOperator.PLUS, c1));
    Expression x2LessThan20 = NumericBooleanExpression.create(x2, NumericComparator.LE, c20);

    Expression init = NumericBooleanExpression.create(x, NumericComparator.EQ, c0);

    Expression complete =
        ExpressionUtil.and(lessThan20, updatex1, x1LessThan20, updatex2, x2LessThan20, init);
    Expression simplified = ExpressionUtil.simplifyAgressiv(complete);
    assertFalse(ExpressionUtil.freeVariables(simplified).contains(x));
    assertFalse(ExpressionUtil.freeVariables(simplified).contains(x1));
    assertFalse(ExpressionUtil.freeVariables(simplified).contains(x2));
  }
}
