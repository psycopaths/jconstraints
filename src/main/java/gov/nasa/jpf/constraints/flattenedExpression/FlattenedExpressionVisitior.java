package gov.nasa.jpf.constraints.flattenedExpression;

import gov.nasa.jpf.constraints.api.ExpressionVisitor;

public interface FlattenedExpressionVisitior<R, D> extends ExpressionVisitor<R, D> {
  public R visit(FlatBooleanExpression n, D data);
}
