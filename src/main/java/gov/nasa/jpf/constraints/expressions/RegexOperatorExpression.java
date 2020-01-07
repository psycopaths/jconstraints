package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

public class RegexOperatorExpression extends AbstractRegExExpression {

	private final Expression<?> left;
	private final RegExOperator operator;
	private final int low;
	private final int high;
	public RegexOperatorExpression(Expression<?> left, RegExOperator operator) {
		this.left=left;
		this.operator=operator;
		this.low = 1;
		this.high = 1;
	}
	public RegexOperatorExpression(Expression<?> left, RegExOperator operator, int low, int high) {
		this.left=left;
		this.operator=operator;
		this.low = low;
		this.high = high;
	}
	public RegexOperatorExpression(Expression<?> left, RegExOperator operator, char low, char high) {
		this.left=left;
		this.operator=operator;
		this.low = low;
		this.high = high;
	}
	
	public RegexOperatorExpression(Expression<?> left, RegExOperator operator, int low) {
		this.left=left;
		this.operator=operator;
		this.low = low;
		this.high = low;
	}
	public static RegexOperatorExpression create(Expression<?>left,RegExOperator operator, int low) {
		if (operator.equals(RegExOperator.LOOP)){
				return new RegexOperatorExpression(left, operator,low);
		}
		return new RegexOperatorExpression(left,operator);
	}
	
	public static RegexOperatorExpression create(Expression<?>left,RegExOperator operator, int low, int high) {
		if (operator.equals(RegExOperator.LOOP)){
			if ((low >= 0 && high >=0) && low<=high) {
				return new RegexOperatorExpression(left, operator,low,high);
			}
			throw new IllegalArgumentException();
		}
		return new RegexOperatorExpression(left,operator);
	}
	
	public static RegexOperatorExpression create(Expression<?> left, RegExOperator operator) {
		return new RegexOperatorExpression(left, operator);
	}
	
	public Expression<?> getLeft() {
		return left;
	}
	
	public RegExOperator getOperator() {
		return operator;
	}
	@Override
	public String evaluate(Valuation values) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);
	}

	@Override
	public Expression<?>[] getChildren() {
		return new Expression[] {left};
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		assert newChildren.length == 2;
	    Expression<?> newLeft = newChildren[0];
	    if(left == newLeft)
	      return this;
	    return new RegexOperatorExpression(newLeft,operator);
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append('(');
		left.print(a, flags);
		a.append(operator.toString());
		a.append(')');
		
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub
		
	}
	public int getLow() {
		return low;
	}
	public int getHigh() {
		return high;
	}
	

}
