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
package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.flattenedExpression.DuplicateFlattenedExpressionVisitor;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

public class SimplificationVisitor<D> extends DuplicateFlattenedExpressionVisitor<D> {
  private static SimplificationVisitor instance;

  public static <E> SimplificationVisitor<E> getInstance() {
    if (instance == null) {
      instance = new SimplificationVisitor<E>();
    }
    return instance;
  }

  @Override
  public Expression visit(FlatBooleanExpression n, D data) {
    Expression[] children = n.getChildren();
    if (children.length == 0) {
      return ExpressionUtil.TRUE;
    }
    if (children.length == 1) {
      return children[0];
    } else {
      HashSet seen = new HashSet<>();
      Expression result = null;
      for (Expression<Boolean> e : n.getChildren()) {
        if (seen.contains(e)) {
          continue;
        }
        seen.add(e);
        Expression convertedChild = e.accept(this, null);
        if (result == null) {
          result = convertedChild;
        } else {
          List<Expression<Boolean>> toCombine = new ArrayList();
          toCombine.add(result);
          toCombine.add(convertedChild);
          result = ExpressionUtil.combine(n.getOperator(), result, toCombine);
        }
      }
      return result;
    }
  }

  @Override
  public Expression<Boolean> visit(LetExpression letExpression, D data) {
    throw new UnsupportedOperationException(
        "The semantics of simplification on a LetExpression is not defined");
  }
}
