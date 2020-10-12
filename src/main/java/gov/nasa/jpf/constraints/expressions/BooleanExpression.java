package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

@Deprecated() // This is completely subsumed by PropositionalCompound
public class BooleanExpression extends AbstractBoolExpression {

	private final Expression<?> left;
	private final Expression<?> right;
	private final BooleanOperator operator;
	
	public static BooleanExpression createEquals(Expression<?> left,Expression<?> right) {
		return new BooleanExpression(left,BooleanOperator.EQ, right);
	}
	public static BooleanExpression createNotEquals(Expression<?> left,Expression<?> right) {
		return new BooleanExpression(left,BooleanOperator.NEQ, right);
	}
	
	public BooleanExpression(Expression<?> left, BooleanOperator operator, Expression<?> right) {
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
	public BooleanOperator getOperator() {
		return operator;
	}
	@Override
	public Boolean evaluate(Valuation values) {
		Boolean lv = (Boolean) left.evaluate(values);
		Boolean rv = (Boolean) right.evaluate(values);
		switch (operator) {
		case EQ:
			return lv==rv;
		case NEQ:
			return lv!=rv;
		default:
			throw new IllegalArgumentException();
		}
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
		left.collectFreeVariables(variables);
		right.collectFreeVariables(variables);
	}

	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);
	}

	@Override
	public Expression<?>[] getChildren() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append("(");
		left.print(a);
		a.append(" |" + operator + "| ");
		right.print(a);
		a.append(")");
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {

	}

}
