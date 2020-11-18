package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import java.util.Set;

public class ExpressionTailoringUtil {
  public static Expression<Boolean> tailor(Expression<Boolean> e, Set<Variable<?>> vars) {
    Expression<Boolean> flattened = e.accept(FlatExpressionVisitor.getInstance(), null);
    return flattened.accept(TailoringVisitor.getInstance(), vars);
  }
}
