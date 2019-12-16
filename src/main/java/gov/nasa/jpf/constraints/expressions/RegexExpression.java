package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class RegexExpression extends AbstractRegExExpression {
	private final Expression<BuiltinTypes.RegExType> left;
	private final Expression<BuiltinTypes.RegExType> right;
	private final RegExOperator operator;
	
	public static RegexExpression create(Expression<BuiltinTypes.RegExType> left, RegExOperator operator, Expression<BuiltinTypes.RegExType> right) {
		return new RegexExpression(left, operator,right);
	}
	
	private RegexExpression(Expression<BuiltinTypes.RegExType> left, RegExOperator operator, Expression<BuiltinTypes.RegExType> right) {
		this.left=left;
		this.right=right;
		this.operator=operator;
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
		// TODO Auto-generated method stub
		return null;
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

	@Override
	public void print(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub

	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub

	}

}
