package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.simplifiers.datastructures.ArithmeticVarReplacements;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.List;

public class NumericSimplificationUtil {

  public static Expression simplify(Expression<?> e) {
    AssignmentCollector collector = new AssignmentCollector();
    CollectAssignmentVisitor visitor = new CollectAssignmentVisitor();
    e.accept(visitor, collector);
    ArithmeticVarReplacements replacements = collector.convertToArithmeticVarReplacements();
    List<Expression> toPrune = collector.getToPrune();

    ExpressionPruningVisitor pruner = new ExpressionPruningVisitor();
    Expression<?> pruned = e.accept(pruner, toPrune);

    Expression replacedExpression = ExpressionUtil.transformVars(pruned, replacements);
    return replacedExpression;
  }
}
