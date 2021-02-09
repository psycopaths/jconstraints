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

package gov.nasa.jpf.constraints.flattenedExpression;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;

public abstract class DuplicateFlattenedExpressionVisitor<D>
    extends AbstractExpressionVisitor<Expression<Boolean>, D>
    implements FlattenedExpressionVisitior<Expression<Boolean>, D> {
  @Override
  public abstract Expression<Boolean> visit(FlatBooleanExpression n, D data);

  @Override
  protected <E> Expression defaultVisit(Expression<E> expression, D data) {
    Expression[] children = expression.getChildren();
    boolean changed = false;
    for (int i = 0; i < children.length; i++) {
      Expression e = children[i];
      Expression result = visit(e, data);
      if (result != e) {
        children[i] = result;
        changed = true;
      }
    }
    if (changed) {
      return expression.duplicate(children);
    }
    return expression;
  }
}
