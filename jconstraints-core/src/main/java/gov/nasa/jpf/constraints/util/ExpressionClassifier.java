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

package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes.BoolType;
import gov.nasa.jpf.constraints.types.BuiltinTypes.DoubleType;
import java.util.ArrayList;
import java.util.List;

public class ExpressionClassifier
    extends AbstractExpressionVisitor<Expression<?>, List<Expression<Boolean>>> {

  protected ExpressionClassifier() {}

  public static Expression<Boolean> getLinearConstraints(Expression<Boolean> constraint) {
    List<Expression<Boolean>> llst = new ArrayList<>();
    splitConstraintsInto(constraint, llst, null, null);
    return (llst.size() > 0) ? ExpressionUtil.and(llst) : null;
  }

  public static Expression<Boolean> getNonLinearConstraints(Expression<Boolean> constraint) {
    List<Expression<Boolean>> nllst = new ArrayList<>();
    splitConstraintsInto(constraint, null, nllst, null);
    return (nllst.size() > 0) ? ExpressionUtil.and(nllst) : null;
  }

  public static Expression<Boolean> getConstantConstraints(Expression<Boolean> constraint) {
    List<Expression<Boolean>> clst = new ArrayList<>();
    splitConstraintsInto(constraint, null, null, clst);
    return (clst.size() > 0) ? ExpressionUtil.and(clst) : null;
  }

  public static List<Expression<Boolean>> splitToConjuncts(Expression<Boolean> constraints) {
    List<Expression<Boolean>> l = new ArrayList<Expression<Boolean>>();
    splitConstraintsInto(constraints, l, l, l);
    return l;
  }

  public static void splitConstraintsInto(
      Expression<Boolean> constraint,
      List<Expression<Boolean>> linearConstraints,
      List<Expression<Boolean>> nonlinearConstraints) {
    splitConstraintsInto(constraint, linearConstraints, nonlinearConstraints, null);
  }

  public static void splitConstraintsInto(
      Expression<Boolean> constraint,
      List<Expression<Boolean>> linearConstraints,
      List<Expression<Boolean>> nonlinearConstraints,
      List<Expression<Boolean>> constants) {
    List<Expression<Boolean>> conjuncts = new ArrayList<Expression<Boolean>>();
    (new ExpressionClassifier()).visit(constraint, conjuncts);
    for (Expression<Boolean> e : conjuncts) {
      switch (ExpressionClassifierVisitor.getInstance().getExpressionType(e)) {
        case CONSTANT:
          if (constants != null) constants.add(e);
          break;
        case LINEAR:
          if (linearConstraints != null) linearConstraints.add(e);
          break;
        case NONLINEAR:
          if (nonlinearConstraints != null) nonlinearConstraints.add(e);
          break;
        default:
          throw new IllegalStateException("Invalid constraint");
      }
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public Expression<Boolean> visit(PropositionalCompound n, List<Expression<Boolean>> data) {
    if (n.getOperator().equals(LogicalOperator.AND)) {
      Expression<?> l = visit(n.getLeft(), data);
      if (l != null) {
        // Must be boolean, but better safe than sorry..
        if (!(l.getType() instanceof BoolType || l.getType() instanceof DoubleType))
          throw new IllegalStateException(
              "Expected operand to be of type "
                  + DoubleType.class.getName()
                  + "; not the provided "
                  + l.getType().getName());
        data.add((Expression<Boolean>) l);
      }
      Expression<?> r = visit(n.getRight(), data);
      if (r != null) {
        if (!(r.getType() instanceof BoolType))
          throw new IllegalStateException(
              "Expected operand to be of type "
                  + DoubleType.class.getName()
                  + "; not the provided "
                  + l.getType().getName());
        data.add((Expression<Boolean>) r);
      }
      return null;
    } else return n;
  }
  ;

  @Override
  public Expression<Boolean> visit(NumericBooleanExpression n, List<Expression<Boolean>> data) {
    data.add(n);
    return null;
  }
  ;

  @Override
  protected <E> Expression<E> defaultVisit(
      Expression<E> expression, List<Expression<Boolean>> data) {
    return expression;
  }
}
