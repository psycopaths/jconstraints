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

package gov.nasa.jpf.constraints.simplifiers;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import org.testng.annotations.Test;

public class DuplicationRemoverTest {

  Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
  Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 3);
  Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "y");
  Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 4);
  Expression lessThanExpression = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
  Expression greaterThan = new NumericBooleanExpression(x2, NumericComparator.LT, c2);
  Expression addition = new NumericCompound(x2, NumericOperator.PLUS, c2);
  Expression assignment = new NumericBooleanExpression(x, NumericComparator.EQ, c2);

  @Test(groups = {"simplifiers", "base"})
  public void simpleDuplicationTest() throws IOException {
    Expression<Boolean> longerExpression =
        ExpressionUtil.and(
            lessThanExpression, lessThanExpression, lessThanExpression, lessThanExpression);

    Expression simplified = ExpressionUtil.simplify(longerExpression);

    Expression<Boolean> withoutDuplication = ExpressionUtil.simplifyAgressiv(longerExpression);

    assertEquals(withoutDuplication, lessThanExpression);
  }

  @Test(groups = {"simplifiers", "base"})
  public void simpleDuplication2Test() {
    Expression<Boolean> longerExpression = ExpressionUtil.and(greaterThan, lessThanExpression);
    longerExpression = ExpressionUtil.or(longerExpression, greaterThan);

    Expression simplified = ExpressionUtil.simplifyAgressiv(longerExpression);
    assertEquals(simplified.toString(), longerExpression.toString());
  }

  @Test(groups = {"simplifiers", "base"})
  public void simpleDuplicationOrTest() {
    Expression firstPart = ExpressionUtil.or(assignment, assignment);
    Expression secondPart = ExpressionUtil.and(lessThanExpression, greaterThan, lessThanExpression);
    Expression<Boolean> thirdPart =
        ExpressionUtil.and(new Negation(firstPart), new Negation(secondPart));

    Expression expected =
        ExpressionUtil.and(
            new Negation(assignment),
            new Negation(ExpressionUtil.and(lessThanExpression, greaterThan)));

    Expression flat = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
    assertEquals(flat.getChildren()[0].getClass(), Negation.class);
    assertEquals(
        ((Negation) flat.getChildren()[0]).getNegated().getClass(), FlatBooleanExpression.class);

    Expression<Boolean> first = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
    Expression second = first.accept(SimplificationVisitor.getInstance(), null);

    assertEquals(second, expected);
  }
}
