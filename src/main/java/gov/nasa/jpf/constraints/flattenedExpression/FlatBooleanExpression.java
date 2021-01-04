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
package gov.nasa.jpf.constraints.flattenedExpression;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class FlatBooleanExpression extends Expression<Boolean> {

  protected ArrayList<Expression<Boolean>> flattenedParts;

  protected LogicalOperator logicalOperator;

  public FlatBooleanExpression(LogicalOperator lo, List<Expression<Boolean>> exprs) {
    this(lo);
    flattenedParts = new ArrayList<>(exprs);
  }

  public FlatBooleanExpression(
      LogicalOperator lo, Expression<Boolean> left, Expression<Boolean> right) {
    this(lo);
    addSubexpression(left);
    addSubexpression(right);
  }

  public FlatBooleanExpression(LogicalOperator lo) {
    logicalOperator = lo;
    flattenedParts = new ArrayList<>();
  }

  @Override
  public Boolean evaluate(final Valuation values) {
    return flattenedParts.stream().map(e -> e.evaluate(values)).reduce((a, b) -> a && b).get();
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    if (visitor instanceof FlattenedExpressionVisitior) {
      return accept((FlattenedExpressionVisitior<R, D>) visitor, data);
    } else {
      throw new RuntimeException("Cannot accept an ExpressionVisitor on flattened Expression.");
    }
  }

  @Override
  public Type<Boolean> getType() {
    return BuiltinTypes.BOOL;
  }

  public FlatBooleanExpression addSubexpression(Expression<Boolean> subExpr) {
    flattenedParts.add(subExpr);
    return this;
  }

  public FlatBooleanExpression addSubexpressions(Expression<Boolean>[] subExprs) {
    flattenedParts.addAll(Arrays.asList(subExprs));
    return this;
  }

  @Override
  public Expression<Boolean>[] getChildren() {
    return flattenedParts.toArray(new Expression[0]);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("(");
    if (flattenedParts.size() > 0) {
      flattenedParts.get(0).print(a, flags);
    }
    for (int i = 1; i < flattenedParts.size(); i++) {
      a.append(" && ");
      flattenedParts.get(i).print(a, flags);
    }
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    a.append("MallformedExpression not supported on FlatBooleanExpression.");
  }

  @Override
  public Expression<?> duplicate(Expression[] newChildren) {
    return new FlatBooleanExpression(logicalOperator, Arrays.asList(newChildren));
  }

  public <R, D> R accept(FlattenedExpressionVisitior<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public void collectFreeVariables(Collection variables) {
    flattenedParts.stream().forEach(e -> e.collectFreeVariables(variables));
  }

  public Expression merge(FlatBooleanExpression expr2) {
    if (this.logicalOperator.equals(expr2.logicalOperator)) {
      return this.addSubexpressions(expr2.getChildren());
    }
    throw new MergeException("Cannot merge Flat Expressions with different Operators");
  }

  public LogicalOperator getOperator() {
    return logicalOperator;
  }
}
