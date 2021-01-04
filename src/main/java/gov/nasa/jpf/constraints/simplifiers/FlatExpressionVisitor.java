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
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.flattenedExpression.DuplicateFlattenedExpressionVisitor;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;

public class FlatExpressionVisitor<D> extends DuplicateFlattenedExpressionVisitor<D> {

  private static FlatExpressionVisitor instance;

  public static <E> FlatExpressionVisitor<E> getInstance() {
    if (instance == null) {
      instance = new FlatExpressionVisitor<E>();
    }
    return instance;
  }

  @Override
  public Expression visit(PropositionalCompound n, D data) {
    Expression newLeft = this.visit(n.getLeft(), data);
    Expression newRight = this.visit(n.getRight(), data);

    if (newLeft instanceof FlatBooleanExpression) {
      FlatBooleanExpression convertedLeft = (FlatBooleanExpression) newLeft;
      if (newRight instanceof FlatBooleanExpression) {
        FlatBooleanExpression convertedRight = (FlatBooleanExpression) newRight;
        if (convertedRight.getOperator().equals(convertedLeft.getOperator())
            && n.getOperator().equals(convertedLeft.getOperator())) {
          return convertedLeft.merge(convertedRight);
        } else if (convertedLeft.getOperator().equals(n.getOperator())) {
          return convertedLeft.addSubexpression(convertedRight);
        } else if (convertedRight.getOperator().equals(n.getOperator())) {
          return convertedRight.addSubexpression(convertedLeft);
        } else {
          return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
        }
      } else {
        if (convertedLeft.getOperator().equals(n.getOperator())) {
          return convertedLeft.addSubexpression(newRight);
        } else {
          return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
        }
      }
    } else {
      if (newRight instanceof FlatBooleanExpression) {
        FlatBooleanExpression convertedRight = (FlatBooleanExpression) newRight;
        if (((FlatBooleanExpression) newRight).getOperator().equals(n.getOperator())) {
          return convertedRight.addSubexpression(newLeft);
        } else {
          return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
        }
      } else {
        return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
      }
    }
  }

  @Override
  public Expression visit(FlatBooleanExpression n, D data) {
    throw new UnsupportedOperationException("This method should not be called");
  }
}
