package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class StringIntegerExpression extends AbstractStringIntegerExpression {

	private final Expression<?> left;
	private final StringIntegerOperator operator;
	private final Expression<?> right;
	private final Expression<?> offset;

	public static StringIntegerExpression createLength(Expression<?> left) {
		return new StringIntegerExpression(left, StringIntegerOperator.LENGTH);
	}

	public static StringIntegerExpression createToInt(Expression<?> left) {
		return new StringIntegerExpression(left, StringIntegerOperator.TOINT);
	}

	public static StringIntegerExpression createIndexOf(Expression<?> left, Expression<?> right, Expression<?> offset) {
		return new StringIntegerExpression(left, StringIntegerOperator.INDEXOF, right, offset);
	}

	public static StringIntegerExpression createIndexOf(Expression<?> left, Expression<?> right) {
		return new StringIntegerExpression(left,
																			 StringIntegerOperator.INDEXOF,
																			 right,
																			 Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0)));
	}

	public Expression<?> getRight() {
		return right;
	}

	public StringIntegerExpression(Expression<?> left, StringIntegerOperator operator) {
		this.left = left;
		this.right = null;
		this.operator = operator;
		this.offset = null;
	}

	public StringIntegerExpression(Expression<?> left,
																 StringIntegerOperator operator,
																 Expression<?> right,
																 Expression<?> offset) {
		this.left = left;
		this.right = right;
		this.operator = operator;
		this.offset = offset;
	}

	@Override
	public BigInteger evaluate(Valuation values) {

		switch (operator) {

			case INDEXOF:
				return evaluateIndexOf(values);
			case LENGTH:
				return evaluateLength(values);
			case TOINT:
				return evaluateToInt(values);
			default:
				throw new IllegalArgumentException();
		}
	}

	private BigInteger evaluateToInt(Valuation values) {
		String lv = (String) left.evaluate(values);
		return BigInteger.valueOf(Integer.valueOf(lv));
	}

	private BigInteger evaluateLength(Valuation values) {
		String string = (String) left.evaluate(values);
		BigInteger length = BigInteger.valueOf(string.length());
		return length;
	}

	private BigInteger evaluateIndexOf(Valuation values) {
		String lv = (String) left.evaluate(values);
		String rv = (String) right.evaluate(values);
		BigInteger of = (BigInteger) offset.evaluate(values);
		return BigInteger.valueOf(lv.indexOf(rv, of.intValue()));
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
		ArrayList<Expression<?>> children = new ArrayList<>();
		checkAndAdd(left, children);
		checkAndAdd(right, children);
		checkAndAdd(offset, children);
		return children.toArray(new Expression[0]);
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		return new StringIntegerExpression(left.duplicate(newChildren),
																			 operator,
																			 right.duplicate(newChildren),
																			 offset.duplicate(newChildren));
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
		a.append("(" + operator + " ");
		switch (operator) {
			case INDEXOF:
				left.print(a, flags);
				right.print(a, flags);
				offset.print(a, flags);
				break;
			case LENGTH:
				left.print(a, flags);
				break;
			case TOINT:
				left.print(a, flags);
				break;
			default:
				throw new IllegalArgumentException();
		}
		a.append(") ");
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		print(a, flags);
	}

	private void checkAndAdd(Expression expr, List<Expression<?>> list) {
		if (expr != null) {
			list.add(expr);
		}
	}

}
