package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class StringIntegerExpression extends AbstractStringIntegerExpression {

	private final Expression<?> left;
	private final StringIntegerOperator operator;
	private final Expression<?> right;
	private final Expression<?> offset;
	
	public static StringIntegerExpression createLength(Expression<?> left) {
		return new StringIntegerExpression(left, StringIntegerOperator.LENGTH);
	}
	public static StringIntegerExpression createToInt (Expression<?> left) {
		return new StringIntegerExpression(left,StringIntegerOperator.TOINT);
	}
	public static StringIntegerExpression createIndexOf(Expression<?> left,Expression<?> right,Expression<?> offset) {
		return new StringIntegerExpression(left,StringIntegerOperator.INDEXOF,right, offset);
	}
	public static StringIntegerExpression createIndexOf(Expression<?> left,Expression<?> right) {
		return new StringIntegerExpression(left,StringIntegerOperator.INDEXOF,right,Constant.create(BuiltinTypes.INTEGER,BigInteger.valueOf(0)));
	}
	public Expression<?> getRight() {
		return right;
	}

	public StringIntegerExpression(Expression<?> left, StringIntegerOperator operator) {
		this.left=left;
		this.right=null;
		this.operator=operator;
		this.offset= null;
	}
	
	public StringIntegerExpression(Expression<?> left, StringIntegerOperator operator, Expression<?> right, Expression<?> offset) {
		this.left=left;
		this.right=right;
		this.operator=operator;
		this.offset=offset;
	}

	@Override
	public BigInteger evaluate(Valuation values) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
	    this.left.collectFreeVariables(variables);
	}

	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);
	}

	@Override
	public Expression<?>[] getChildren() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		// TODO Auto-generated method stub
		return null;
	}

	public Expression<?> getLeft() {
		return left;
	}

	public StringIntegerOperator getOperator() {
		return operator;
	}

	public Expression<?> getOffset() {
		return offset;
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub
		
	}


}
