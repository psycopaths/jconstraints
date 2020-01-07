package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class RegexCompoundExpression extends AbstractRegExExpression {
	private final Expression<?> left;
	private final Expression<?> right;
	private final RegExCompoundOperator operator;

	public static RegexCompoundExpression create(Expression<?> left, RegExCompoundOperator operator, Expression<?> right) {
		return new RegexCompoundExpression(left, operator,right);
	}
	public static RegexCompoundExpression create(Expression<?>left, RegExCompoundOperator operator, Expression<?> ...expressions) {
		RegexCompoundExpression result;
		if (expressions.length>=1 && left != null) {
			result = new RegexCompoundExpression(left, operator,expressions[0]);
			for (int i = 1; i<expressions.length;i++) {
				result = new RegexCompoundExpression(result, RegExCompoundOperator.CONCAT,expressions[i]);
			}
			return result;
		}
		throw new IllegalArgumentException();
	}
	private RegexCompoundExpression(Expression<?> left, RegExCompoundOperator operator, Expression<?> right) {
		this.left=left;
		this.right=right;
		this.operator=operator;
	}
	
	public Expression<?> getLeft() {
		return left;
	}

	public Expression<?> getRight() {
		return right;
	}

	public RegExCompoundOperator getOperator() {
		return operator;
	}
	
	@Override
	public String evaluate(Valuation values) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException(this.getClass().getName() + ": evaluate is not Implemented");
		//return null;
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
		// TODO Auto-generated method stub

	}

	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		// TODO Auto-generated method stub
		return visitor.visit(this,data);
	}

	@Override
	public Expression<?>[] getChildren() {
		return new Expression [] {left,right};
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		assert newChildren.length == 2;
	    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
	    if(left == newLeft && right == newRight)
	      return this;
	    return new RegexCompoundExpression(newLeft,operator,newRight);
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append('(');
		left.print(a, flags);
		a.append(operator.toString());
		right.print(a,flags);
		a.append(')');

	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub

	}

}
