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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.List;

public class ExpressionPruningVisitor extends DuplicatingVisitor<List<Expression>> {

  @Override
  public Expression visit(PropositionalCompound n, List<Expression> data) {
    Expression left = n.getLeft().accept(this, data);
    Expression right = n.getRight().accept(this, data);

    if (left.equals(ExpressionUtil.TRUE)) {
      return right;
    } else if (right.equals(ExpressionUtil.TRUE)) {
      return left;
    } else {
      return new PropositionalCompound(left, n.getOperator(), right);
    }
  }

  @Override
  public Expression<?> visit(LetExpression letExpression, List<Expression> data) {
    throw new UnsupportedOperationException(
        "The semantics of expression pruning for LetExpressions is not yet defined");
  }

  @Override
  public Expression visit(NumericBooleanExpression n, List<Expression> data) {
    if (data.contains(n)) {
      return ExpressionUtil.TRUE;
    }
    return n;
  }
}
