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
