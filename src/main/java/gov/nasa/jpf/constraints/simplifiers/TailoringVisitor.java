package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.flattenedExpression.DuplicateFlattenedExpressionVisitor;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TailoringVisitor extends DuplicateFlattenedExpressionVisitor<Collection<Variable<?>>> {
  private static TailoringVisitor instance;

  public static TailoringVisitor getInstance() {
    if (instance == null) {
      instance = new TailoringVisitor();
    }
    return instance;
  }

  @Override
  public Expression<Boolean> visit(FlatBooleanExpression n, Collection<Variable<?>> data) {
    Expression[] children = n.getChildren();
    long debug = System.currentTimeMillis();

    Set<Variable<?>> vars = new HashSet<>(data);
    List<Expression<Boolean>> shouldConvert = new ArrayList();
    boolean reiterate = true;
    while (reiterate) {
      reiterate = false;
      for (Expression<Boolean> child : children) {
        Expression convertedChild = child.accept(this, vars);
        if (shouldConvert.contains(convertedChild)) {
          continue;
        }
        Set<Variable<?>> varsInChild = ExpressionUtil.freeVariables(convertedChild);

        for (Variable var : varsInChild) {
          if (vars.contains(var)) {
            vars.addAll(varsInChild);
            shouldConvert.add(convertedChild);
            reiterate = true;
            break;
          }
        }
      }
    }
    if (shouldConvert.size() == 0) {
      return ExpressionUtil.TRUE;
    }
    if (shouldConvert.size() == 1) {
      return shouldConvert.get(0);
    } else {
      Expression result = shouldConvert.get(0);
      for (int i = 1; i < shouldConvert.size(); i++) {
        result = ExpressionUtil.and(result, shouldConvert.get(i));
      }
      return result;
    }
  }

  @Override
  public Expression<Boolean> visit(LetExpression letExpression, Collection<Variable<?>> data) {
    throw new UnsupportedOperationException(
        "The semantics of a tailoring visitor for LetExpressions is not yet designed");
  }
}
