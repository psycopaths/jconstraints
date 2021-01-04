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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.types.TypeContext;
import java.io.IOException;
import java.util.Collection;

/** Numeric expression */
public class NumericCompound<E> extends AbstractExpression<E> {

  public static Expression<?> createCompatible(
      Expression<?> left, NumericOperator op, Expression<?> right, TypeContext types) {
    Type<?> lt = left.getType(), rt = right.getType();
    Type<?> superType = types.mostSpecificSupertype(lt, rt);
    Expression<?> l = (superType.equals(lt)) ? left : CastExpression.create(left, superType);
    Expression<?> r = (superType.equals(rt)) ? right : CastExpression.create(right, superType);
    return create(l, op, r);
  }

  public static <E> NumericCompound<E> create(
      Expression<E> left, NumericOperator operator, Expression<?> right) {
    Type<E> type = left.getType();
    Expression<E> r = right.requireAs(type);
    return new NumericCompound<>(left, operator, r);
  }

  private final NumericOperator operator;
  private final Expression<E> left;
  private final Expression<E> right;

  public NumericCompound(Expression<E> left, NumericOperator operator, Expression<E> right) {
    assert left.getType() instanceof NumericType;
    assert right.getType().equals(left.getType());

    this.operator = operator;
    this.left = left;
    this.right = right;
  }

  @Override
  public E evaluate(Valuation values) {
    E lv = left.evaluate(values);
    E rv = right.evaluate(values);

    NumericType<E> type = (NumericType<E>) getType();
    switch (operator) {
      case PLUS:
        return type.plus(lv, rv);
      case MINUS:
        return type.minus(lv, rv);
      case MUL:
        return type.mul(lv, rv);
      case DIV:
        return type.div(lv, rv);
      case REM:
        return type.mod(lv, rv);
      default:
        throw new IllegalStateException("Unknown numeric operator " + operator);
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    left.collectFreeVariables(variables);
    right.collectFreeVariables(variables);
  }

  /** @return the comparator */
  public NumericOperator getOperator() {
    return this.operator;
  }

  public Expression<E> getLeft() {
    return left;
  }

  public Expression<E> getRight() {
    return right;
  }

  @Override
  public Type<E> getType() {
    return left.getType();
  }

  @Override
  @SuppressWarnings("unchecked")
  public Expression<E>[] getChildren() {
    return new Expression[] {left, right};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 2;

    if (identical(newChildren, left, right)) return this;

    return create(newChildren[0], operator, newChildren[1]);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(');
    left.print(a, flags);
    a.append(' ').append(operator.toString()).append(' ');
    right.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    a.append('(');
    if (left == null) {
      a.append("null");
    } else {
      left.printMalformedExpression(a, flags);
    }
    a.append(' ').append(operator.toString()).append(' ');
    if (right == null) {
      a.append("null");
    } else {
      right.printMalformedExpression(a, flags);
    }
    a.append(')');
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + left.hashCode();
    result = prime * result + operator.hashCode();
    result = prime * result + right.hashCode();
    return result;
  }

  /* (non-Javadoc)
   * @see java.lang.Object#equals(java.lang.Object)
   */
  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    NumericCompound<?> other = (NumericCompound<?>) obj;
    if (operator != other.operator) {
      return false;
    }

    return left.equals(other.left) && right.equals(other.right);
  }

  public <F> Expression<F> as(Type<F> type) {
    Type<E> thisType = getType();
    if (!thisType.equals(type)) {
      if (thisType.equals(BuiltinTypes.INTEGER) && type.equals(BuiltinTypes.DECIMAL)) {
        if ((left instanceof Constant
                || left instanceof UnaryMinus
                    && ((UnaryMinus) left).getNegated() instanceof Constant)
            && (right instanceof Constant
                || right instanceof UnaryMinus
                    && ((UnaryMinus) right).getNegated() instanceof Constant)) {
          Expression newLeft, newRight;
          if (left instanceof UnaryMinus) {
            newLeft =
                new UnaryMinus(
                    new Constant(type, ((Constant) ((UnaryMinus) left).getNegated()).getValue()));
          } else {
            newLeft = new Constant(type, ((Constant) left).getValue());
          }
          if (right instanceof UnaryMinus) {
            newRight =
                new UnaryMinus(
                    new Constant(type, ((Constant) ((UnaryMinus) right).getNegated()).getValue()));
          } else {
            newRight = new Constant(type, ((Constant) right).getValue());
          }

          return new NumericCompound(newLeft, this.operator, newRight);
        }
      }
      return null;
    }
    return (Expression<F>) this;
  }
}
