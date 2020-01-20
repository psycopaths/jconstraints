package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

public class StringBooleanExpression extends AbstractBoolExpression {
	public static StringBooleanExpression createEquals (Expression<?> left,Expression<?> right) {
		return new StringBooleanExpression(left,StringBooleanOperator.EQUALS,right);
	}
	public static StringBooleanExpression createContains (Expression<?> left,Expression<?> right) {
		return new StringBooleanExpression(left,StringBooleanOperator.CONTAINS,right);
	}
	public static StringBooleanExpression createPrefixOf (Expression<?> left,Expression<?> right) {
		return new StringBooleanExpression(left,StringBooleanOperator.PREFIXOF,right);
	}
	public static StringBooleanExpression createSuffixOf (Expression<?> left,Expression<?> right) {
		return new StringBooleanExpression(left,StringBooleanOperator.SUFFIXOF,right);
	}
	private final Expression<?> left;
	private final Expression<?> right;
	private final StringBooleanOperator operator;
	public StringBooleanExpression(Expression<?> left,StringBooleanOperator operator, Expression<?> right) {
		this.left=left;
		this.right=right;
		this.operator=operator;
	}
	
	public Expression<?> getLeft() {
	    return this.left;
	}
	
	public Expression<?> getRight(){
		return this.right;
	}
	
	public StringBooleanOperator getOperator() {
		return this.operator;
	}
	
	@Override
	public Boolean evaluate(Valuation values) {
		//throw new UnsupportedOperationException();
		return null;
	}


	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);		
	}

	@Override
	public Expression<?>[] getChildren() {
		return new Expression[]{left, right};
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		assert newChildren.length == 2;
	    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
	    if(left == newLeft && right == newRight)
	      return this;
	    return new StringBooleanExpression(newLeft,this.operator,newRight);
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append("(");
		a.append(operator.toString());
		left.print(a,flags);
		right.print(a, flags);
		a.append(")");
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		throw new UnsupportedOperationException();

	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
	    this.left.collectFreeVariables(variables);
	    this.right.collectFreeVariables(variables);
	}
	

}
