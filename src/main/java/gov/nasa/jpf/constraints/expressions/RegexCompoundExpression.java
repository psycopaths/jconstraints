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
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.io.IOException;
import java.util.Collection;

public class RegexCompoundExpression extends AbstractRegExExpression {
  private final Expression<?> left;
  private final Expression<?> right;
  private final RegExCompoundOperator operator;

  public static RegexCompoundExpression createUnion(Expression<?> left, Expression<?> right) {
    return new RegexCompoundExpression(left, RegExCompoundOperator.UNION, right);
  }

  public static RegexCompoundExpression createIntersection(
      Expression<?> left, Expression<?> right) {
    return new RegexCompoundExpression(left, RegExCompoundOperator.INTERSECTION, right);
  }

  public static RegexCompoundExpression createConcat(Expression<?>... expressions) {
    RegexCompoundExpression result;
    if (expressions.length >= 2) {
      result =
          new RegexCompoundExpression(expressions[0], RegExCompoundOperator.CONCAT, expressions[1]);
      for (int i = 2; i < expressions.length; i++) {
        result = new RegexCompoundExpression(result, RegExCompoundOperator.CONCAT, expressions[i]);
      }
      return result;
    }
    throw new IllegalArgumentException();
  }

  private RegexCompoundExpression(
      Expression<?> left, RegExCompoundOperator operator, Expression<?> right) {
    this.left = left;
    this.right = right;
    this.operator = operator;
  }

  public Expression<?> getLeft() {
    return left;
  }

  public Expression<?> getRight() {
    return right;
  }

  public RegExCompoundOperator getOperator() {
    return operator;
  }

  @Override
  public String evaluate(Valuation values) {
    String lv = (String) left.evaluate(values);
    String rv = (String) right.evaluate(values);
    return computeCompound(lv, rv);
  }

  @Override
  public String evaluateSMT(Valuation values) {
    String lv = (String) left.evaluate(values);
    String rv = (String) right.evaluate(values);
    return computeCompound(lv, rv);
  }

  private String computeCompound(String lv, String rv) {
    switch (operator) {
      case CONCAT:
        return lv + rv;
      case INTERSECTION:
        return "((?=" + lv + ")" + rv + ")";
      case UNION:
        return "(" + lv + "|" + rv + ")";
      default:
        throw new IllegalArgumentException();
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    left.collectFreeVariables(variables);
    right.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    // TODO Auto-generated method stub
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
    if (left == newLeft && right == newRight) return this;
    return new RegexCompoundExpression(newLeft, operator, newRight);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    // TODO this doesn't really work
    a.append("(" + operator + " ");
    left.print(a, flags);
    right.print(a, flags);
    a.append(") ");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    // TODO Auto-generated method stub

  }
}
