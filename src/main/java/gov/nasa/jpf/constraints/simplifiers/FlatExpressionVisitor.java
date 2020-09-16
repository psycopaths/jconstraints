package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.flattenedExpression.DuplicateFlattenedExpressionVisitor;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;

public class FlatExpressionVisitor<D> extends DuplicateFlattenedExpressionVisitor<D> {

    private static FlatExpressionVisitor instance;

    public static <E> FlatExpressionVisitor<E> getInstance(){
        if(instance == null){
            instance = new FlatExpressionVisitor<E>();
        }
        return instance;
    }
    @Override
    public Expression visit(PropositionalCompound n, D data) {
        Expression newLeft = this.visit(n.getLeft(), data);
        Expression newRight = this.visit(n.getRight(), data);

        if (newLeft instanceof FlatBooleanExpression) {
            FlatBooleanExpression convertedLeft = (FlatBooleanExpression) newLeft;
            if (newRight instanceof FlatBooleanExpression) {
                FlatBooleanExpression convertedRight = (FlatBooleanExpression) newRight;
                if (convertedRight.getOperator().equals(convertedLeft.getOperator()) && n.getOperator().equals(convertedLeft.getOperator())) {
                    return convertedLeft.merge(convertedRight);
                } else if (convertedLeft.getOperator().equals(n.getOperator())) {
                    return convertedLeft.addSubexpression(convertedRight);
                } else if (convertedRight.getOperator().equals(n.getOperator())) {
                    return convertedRight.addSubexpression(convertedLeft);
                } else {
                    return new FlatBooleanExpression(n.getOperator(),newLeft, newRight);
                }
            } else {
                if (convertedLeft.getOperator().equals(n.getOperator())) {
                    return convertedLeft.addSubexpression(newRight);
                } else {
                    return new FlatBooleanExpression(n.getOperator(),newLeft, newRight);
                }
            }
        } else {
            if (newRight instanceof FlatBooleanExpression) {
                FlatBooleanExpression convertedRight = (FlatBooleanExpression) newRight;
                if (((FlatBooleanExpression) newRight).getOperator().equals(n.getOperator())) {
                    return convertedRight.addSubexpression(newLeft);
                } else {
                    return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
                }
            } else {
                return new FlatBooleanExpression(n.getOperator(), newLeft, newRight);
            }
        }
    }

    @Override
    public Expression<Boolean> visit(LetExpression letExpression, D data) {
        throw new UnsupportedOperationException("The semantics of a Flat-Expression Visitor is not yet defined");
    }


    @Override
    public Expression visit(FlatBooleanExpression n, D data) {
        throw new UnsupportedOperationException("This method should not be called");
    }
}
