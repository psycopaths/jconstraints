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
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;

/** abstract base for visitors */
public abstract class AbstractExpressionVisitor<R, D> implements ExpressionVisitor<R, D> {

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, D)
   */
  @Override
  public <E> R visit(Variable<E> v, D data) {
    return defaultVisit(v, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.Constant, D)
   */
  @Override
  public <E> R visit(Constant<E> c, D data) {
    return defaultVisit(c, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.Negation, D)
   */
  @Override
  public R visit(Negation n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.NumericBooleanExpression, D)
   */
  @Override
  public R visit(NumericBooleanExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(RegExBooleanExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(StringBooleanExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(StringIntegerExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(StringCompoundExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(RegexCompoundExpression n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(RegexOperatorExpression n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.CastExpression, D)
   */
  @Override
  public <F, E> R visit(CastExpression<F, E> cast, D data) {
    return defaultVisit(cast, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.NumericCompound, D)
   */
  @Override
  public <E> R visit(NumericCompound<E> n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.IfThenElse, D)
   */
  @Override
  public <E> R visit(IfThenElse<E> n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.PropositionalCompound, D)
   */
  @Override
  public R visit(PropositionalCompound n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.UnaryMinus, D)
   */
  @Override
  public <E> R visit(UnaryMinus<E> n, D data) {
    return defaultVisit(n, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.QuantifierExpression, D)
   */
  @Override
  public R visit(QuantifierExpression q, D data) {
    return defaultVisit(q, data);
  }

  @Override
  public <E> R visit(FunctionExpression<E> f, D data) {
    return defaultVisit(f, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.BitvectorExpression, java.lang.Object)
   */
  @Override
  public <E> R visit(BitvectorExpression<E> bv, D data) {
    return defaultVisit(bv, data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
   * .BitvectorNegation, java.lang.Object)
   */
  @Override
  public <E> R visit(BitvectorNegation<E> n, D data) {
    return defaultVisit(n, data);
  }

  @Override
  public R visit(LetExpression let, D data) {
    return defaultVisit(let, data);
  }

  protected <E> R defaultVisit(Expression<E> expression, D data) {
    throw new UnsupportedOperationException();
  }

  protected final R visit(Expression<?> expression, D data) {
    return expression.accept(this, data);
  }

  protected final R visit(Expression<?> expression) {
    return visit(expression, null);
  }
}
