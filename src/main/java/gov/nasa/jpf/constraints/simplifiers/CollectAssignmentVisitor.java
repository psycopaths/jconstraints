package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class CollectAssignmentVisitor extends AbstractExpressionVisitor<Expression, AssignmentCollector> {

    @Override
    public Expression visit(NumericBooleanExpression n, AssignmentCollector data) {
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
    public Expression visit(LetExpression letExpression, AssignmentCollector data) {
        throw new UnsupportedOperationException("The semantics of an collect assignment visitor is not yet defined");

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
