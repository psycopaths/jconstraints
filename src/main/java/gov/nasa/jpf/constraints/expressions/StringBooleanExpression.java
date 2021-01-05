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

import static com.google.common.base.Preconditions.checkNotNull;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.io.IOException;
import java.util.Collection;

public class StringBooleanExpression extends AbstractBoolExpression {

  private final Expression<?> left;
  private final Expression<?> right;
  private final StringBooleanOperator operator;

  public StringBooleanExpression(
      Expression<?> left, StringBooleanOperator operator, Expression<?> right) {
    checkNotNull(left);
    checkNotNull(right);
    checkNotNull(operator);
    this.left = left;
    this.right = right;
    this.operator = operator;
  }

  public static StringBooleanExpression createEquals(Expression<?> left, Expression<?> right) {
    return new StringBooleanExpression(left, StringBooleanOperator.EQUALS, right);
  }

  public static StringBooleanExpression createContains(Expression<?> left, Expression<?> right) {
    return new StringBooleanExpression(left, StringBooleanOperator.CONTAINS, right);
  }

  public static StringBooleanExpression createPrefixOf(Expression<?> left, Expression<?> right) {
    return new StringBooleanExpression(left, StringBooleanOperator.PREFIXOF, right);
  }

  public static StringBooleanExpression createSuffixOf(Expression<?> left, Expression<?> right) {
    return new StringBooleanExpression(left, StringBooleanOperator.SUFFIXOF, right);
  }

  public Expression<?> getLeft() {
    return this.left;
  }

  public Expression<?> getRight() {
    return this.right;
  }

  public StringBooleanOperator getOperator() {
    return this.operator;
  }

  @Override
  public Boolean evaluate(Valuation values) {

    switch (operator) {
      case CONTAINS:
        return evaluateContains(left, right, values);
      case EQUALS:
        return evaluateEquals(left, right, values);
      case PREFIXOF:
        return evaluatePrefixOf(left, right, values);
      case SUFFIXOF:
        return evaluateSuffixOf(left, right, values);
      default:
        throw new IllegalArgumentException();
    }
  }

  private Boolean evaluateSuffixOf(Expression<?> left, Expression<?> right, Valuation values) {
    String lv = (String) left.evaluate(values);
    String rv = (String) right.evaluate(values);
    return lv.endsWith(rv);
  }

  private <L, R> Boolean evaluatePrefixOf(
      Expression<L> left, Expression<R> right, Valuation values) {
    String lv = (String) left.evaluate(values);
    String rv = (String) right.evaluate(values);
    return lv.startsWith(rv);
  }

  private <L, R> Boolean evaluateContains(
      Expression<L> left, Expression<R> right, Valuation values) {
    String lv = (String) left.evaluate(values);
    String rv = (String) right.evaluate(values);
    return lv.contains(rv);
  }

  @SuppressWarnings("unlikely-arg-type")
  private <L, R> Boolean evaluateEquals(Expression<L> left, Expression<R> right, Valuation values) {

    L lv = left.evaluate(values);
    R rv = right.evaluate(values);
    return lv.equals(rv);
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
    return new StringBooleanExpression(newLeft, this.operator, newRight);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(");
    a.append(operator.toString());
    left.print(a, flags);
    right.print(a, flags);
    a.append(") ");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    throw new UnsupportedOperationException();
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.left.collectFreeVariables(variables);
    this.right.collectFreeVariables(variables);
  }
}
