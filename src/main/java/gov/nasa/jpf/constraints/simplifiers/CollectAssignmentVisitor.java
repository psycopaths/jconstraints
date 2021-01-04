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
package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class CollectAssignmentVisitor
    extends AbstractExpressionVisitor<Expression, AssignmentCollector> {

  @Override
  public <E> Expression visit(NumericBooleanExpression n, AssignmentCollector data) {
    Expression left = n.getLeft();
    Expression right = n.getRight();

    if (n.getComparator().equals(NumericComparator.EQ) && !data.isNegation()) {
      if (left instanceof Variable) {
        data.addAssignment((Variable) left, right, n);
      } else if (right instanceof Variable) {
        data.addAssignment((Variable) right, left, n);
      } else {
        for (Variable v : ExpressionUtil.freeVariables(n)) {
          data.addAssignment(v, n, n);
        }
      }
    }
    defaultVisit(n, data);
    return n;
  }

  @Override
  public Expression visit(Negation n, AssignmentCollector data) {
    data.enterNegation();
    this.visit(n.getNegated(), data);
    data.exitNegation();
    return n;
  }

  @Override
  protected <E> Expression defaultVisit(Expression<E> expression, AssignmentCollector data) {
    for (Expression e : expression.getChildren()) {
      e.accept(this, data);
    }
    return expression;
  }
}
