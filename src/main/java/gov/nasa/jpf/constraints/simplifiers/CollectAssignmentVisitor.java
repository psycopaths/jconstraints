package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.Map;

public class CollectAssignmentVisitor extends AbstractExpressionVisitor<Expression, AssignmentCollector> {

    public <E>
    Expression visit(NumericBooleanExpression n, AssignmentCollector data) {
        Expression left = n.getLeft();
        Expression right = n.getRight();

        if (n.getComparator().equals(NumericComparator.EQ)){
            if (left instanceof Variable) {
                data.addAssignment((Variable) left, right, n);
            } else if(right instanceof Variable) {
                data.addAssignment((Variable) right, left, n);
            } else {
                for(Variable v: ExpressionUtil.freeVariables(n)){
                    data.addAssignment(v, n, n);
                }
            }
        }
        defaultVisit(n, data);
        return n;
    }

    @Override
    protected <E> Expression defaultVisit(Expression<E> expression, AssignmentCollector data) {
        for(Expression e: expression.getChildren()){
            e.accept(this, data);
        }
        return expression;
    }

}
