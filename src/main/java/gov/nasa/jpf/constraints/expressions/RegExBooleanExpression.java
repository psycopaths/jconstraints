package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class RegExBooleanExpression extends AbstractBoolExpression {
	public static RegExBooleanExpression create (Expression<?> regex,Expression<?> string) {
		return new RegExBooleanExpression(regex,string);
	}
	private final Expression<?> regex;
	private final Expression<?> string;
	public RegExBooleanExpression(Expression<?> regex,Expression<?> string) {
		this.regex=regex;
		this.string=string;
	}
	
	public Expression<?> getRegex() {
	    return this.regex;
	}
	
	public Expression<?> getString(){
		return this.string;
	}
	@Override
	public Boolean evaluate(Valuation values) {
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
