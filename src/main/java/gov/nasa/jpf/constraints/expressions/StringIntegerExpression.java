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
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class StringIntegerExpression extends AbstractStringIntegerExpression {

  private final Expression<?> left;
  private final StringIntegerOperator operator;
  private final Expression<?> right;
  private final Expression<?> offset;

  private StringIntegerExpression(Expression<?> left, StringIntegerOperator operator) {
    this.left = left;
    this.right = null;
    this.operator = operator;
    this.offset = null;
  }

  private StringIntegerExpression(
      Expression<?> left,
      StringIntegerOperator operator,
      Expression<?> right,
      Expression<?> offset) {
    this.left = left;
    this.right = right;
    this.operator = operator;
    this.offset = offset;
  }

  public static StringIntegerExpression createLength(Expression<?> left) {
    return new StringIntegerExpression(left, StringIntegerOperator.LENGTH);
  }

  public static StringIntegerExpression createToInt(Expression<?> left) {
    return new StringIntegerExpression(left, StringIntegerOperator.TOINT);
  }

  public static StringIntegerExpression createIndexOf(
      Expression<?> left, Expression<?> right, Expression<?> offset) {
    if (offset == null) {
      return createIndexOf(left, right);
    }
    return new StringIntegerExpression(left, StringIntegerOperator.INDEXOF, right, offset);
  }

  public static StringIntegerExpression createIndexOf(Expression<?> left, Expression<?> right) {
    return new StringIntegerExpression(
        left,
        StringIntegerOperator.INDEXOF,
        right,
        Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO));
  }

  public Expression<?> getRight() {
    return right;
  }

  @Override
  public BigInteger evaluate(Valuation values) {
    String lv = (String) left.evaluate(values);
    switch (operator) {
      case INDEXOF:
        String rv = (String) right.evaluate(values);
        BigInteger of = offset != null ? (BigInteger) offset.evaluate(values) : BigInteger.ZERO;
        return BigInteger.valueOf(lv.indexOf(rv, of.intValue()));
      case LENGTH:
        return BigInteger.valueOf(lv.length());
      case TOINT:
        return BigInteger.valueOf(Integer.valueOf(lv));
      default:
        throw new IllegalArgumentException();
    }
  }

  @Override
  public BigInteger evaluateSMT(Valuation values) {
    String lv = (String) left.evaluateSMT(values);
    switch (operator) {
      case INDEXOF:
        String rv = (String) right.evaluateSMT(values);
        BigInteger of = offset != null ? (BigInteger) offset.evaluateSMT(values) : BigInteger.ZERO;
        int index = lv.indexOf(rv, of.intValue());
        if (index == -1 && of.intValue() >= 0 && of.intValue() <= lv.length() && rv.equals("")) {
          index = of.intValue();
        }
        return BigInteger.valueOf(index);
      case LENGTH:
        return BigInteger.valueOf(lv.length());
      case TOINT:
        return BigInteger.valueOf(Integer.valueOf(lv));
      default:
        throw new IllegalArgumentException();
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.left.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Expression<?>[] getChildren() {
    ArrayList<Expression<?>> children = new ArrayList<>();
    checkAndAdd(left, children);
    checkAndAdd(right, children);
    checkAndAdd(offset, children);
    return children.toArray(new Expression[0]);
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    return new StringIntegerExpression(
        left.duplicate(newChildren),
        operator,
        right.duplicate(newChildren),
        offset != null ? offset.duplicate(newChildren) : null);
  }

  public Expression<?> getLeft() {
    return left;
  }

  public StringIntegerOperator getOperator() {
    return operator;
  }

  public Expression<?> getOffset() {
    return offset;
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(" + operator + " ");
    switch (operator) {
      case INDEXOF:
        left.print(a, flags);
        a.append(" ");
        right.print(a, flags);
        if (offset != null) {
          a.append(" ");
          offset.print(a, flags);
        }
        break;
      case LENGTH:
        left.print(a, flags);
        break;
      case TOINT:
        left.print(a, flags);
        break;
      default:
        throw new IllegalArgumentException();
    }
    a.append(") ");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    print(a, flags);
  }

  private void checkAndAdd(Expression expr, List<Expression<?>> list) {
    if (expr != null) {
      list.add(expr);
    }
  }
}
