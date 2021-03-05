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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.io.IOException;
import java.util.Collection;

public class RegExBooleanExpression extends AbstractBoolExpression {
  public static RegExBooleanExpression create(Expression<?> left, Expression<?> right) {
    return new RegExBooleanExpression(left, right);
  }

  private final Expression<?> left;
  private final Expression<?> right;

  public RegExBooleanExpression(Expression<?> left, Expression<?> right) {
    this.left = left;
    this.right = right;
  }

  public Expression<?> getLeft() {
    return this.left;
  }

  public Expression<?> getRight() {
    return this.right;
  }

  @Override
  public Boolean evaluate(Valuation values) {
    String stringExpression = (String) left.evaluate(values);
    String regexExpression = (String) right.evaluate(values);
    return stringExpression.matches(regexExpression);
  }

  @Override
  public Boolean evaluateSMT(Valuation values) {
    String stringExpression = (String) left.evaluateSMT(values);
    String regexExpression = (String) right.evaluateSMT(values);
    return stringExpression.matches(regexExpression);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[] {left, right};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 2;
    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
    if (left == newLeft && right == newRight) {
      return this;
    }
    return new RegExBooleanExpression(newLeft, newRight);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(str.in.re ");
    left.print(a, flags);
    right.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    // throw new UnsupportedOperationException();

  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.left.collectFreeVariables(variables);
    this.right.collectFreeVariables(variables);
  }
}
