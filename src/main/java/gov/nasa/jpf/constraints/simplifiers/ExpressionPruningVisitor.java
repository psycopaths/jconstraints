package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

import java.util.List;

public class ExpressionPruningVisitor extends DuplicatingVisitor<List<Expression>> {


    @Override
    public Expression visit(PropositionalCompound n, List<Expression> data) {
        Expression left = n.getLeft().accept(this, data);
        Expression right = n.getRight().accept(this, data);

        if(left.equals(ExpressionUtil.TRUE)){
            return right;
        } else if(right.equals(ExpressionUtil.TRUE)) {
            return left;
        } else {
            return new PropositionalCompound(left, n.getOperator(), right);
        }
    }

    @Override
    public <E> Expression visit(NumericBooleanExpression n, List<Expression> data) {
        if(data.contains(n)){
            return ExpressionUtil.TRUE;
        }
        return n;
    }

}
