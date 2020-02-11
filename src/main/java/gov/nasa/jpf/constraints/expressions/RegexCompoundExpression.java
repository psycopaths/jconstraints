package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

public class RegexCompoundExpression extends AbstractRegExExpression {
	private final Expression<?> left;
	private final Expression<?> right;
	private final RegExCompoundOperator operator;

	public static RegexCompoundExpression createUnion(Expression<?> left,Expression<?> right) {
		return new RegexCompoundExpression(left,RegExCompoundOperator.UNION,right);
	}
	public static RegexCompoundExpression createIntersection(Expression<?> left,Expression<?> right) {
		return new RegexCompoundExpression(left,RegExCompoundOperator.INTERSECTION,right);
	}
	public static RegexCompoundExpression createConcat(Expression<?> ...expressions) {
		RegexCompoundExpression result;
		if (expressions.length>=2) {
			result = new RegexCompoundExpression(expressions[0],RegExCompoundOperator.CONCAT,expressions[1]);
			for (int i = 2; i<expressions.length;i++) {
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
		switch(operator) {
		case CONCAT:
			return evaluateConcat(values);
		case INTERSECTION:
			return evaluateIntersection(values);
		case UNION:
			return evaluateUnion(values);
		default:
			throw new IllegalArgumentException();
		}
	}

	private String evaluateUnion(Valuation values) {
		String lv = (String)left.evaluate(values);
		String rv = (String)right.evaluate(values);
		return "(" + lv + "|" + rv + ")";
	}
	private String evaluateIntersection(Valuation values) {
		String lv = (String)left.evaluate(values);
		String rv = (String)right.evaluate(values);
		return "((?=" + lv + ")" + rv + ")";
	}
	private String evaluateConcat(Valuation values) {
		String lv = (String)left.evaluate(values);
		String rv = (String)right.evaluate(values);
		return "(" + lv + rv + ")";
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
