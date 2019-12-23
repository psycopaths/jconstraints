package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.math.BigDecimal;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;

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
		//throw new UnsupportedOperationException();
		return null;
	}


	@Override
	public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
		return visitor.visit(this, data);
		
	}

	@Override
	public Expression<?>[] getChildren() {
		return new Expression[]{regex, string};
	}

	@Override
	public Expression<?> duplicate(Expression<?>[] newChildren) {
		assert newChildren.length == 2;
	    Expression<?> newLeft = newChildren[0], newRight = newChildren[1];
	    if(regex == newLeft && string == newRight)
	      return this;
	    return new RegExBooleanExpression(newLeft,newRight);
	}

	@Override
	public void print(Appendable a, int flags) throws IOException {
		a.append('(');
		string.print(a, flags);
		a.append(" MATCHES: ");
		regex.print(a,flags);
		a.append(')');

	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		//throw new UnsupportedOperationException();

	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
		// TODO Auto-generated method stub
	}
	

}
