package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

public class StringCompoundExpression extends AbstractStringExpression {

	private final Expression<?> main;
	private final Expression<?>[] expressions;
	private final Expression<?> dst;
	private final StringOperator operator;
	private final Expression<?> offset;
	private final Expression<?> length;
	private final Expression<?> position;
	private final Expression<?> src;

	public static StringCompoundExpression createConcat (Expression<?> ... expressions) {
		if (expressions.length>1) {
			System.out.println("Expressions in StringCompoundExpression: " + Arrays.toString(expressions));
			return new StringCompoundExpression(null,StringOperator.CONCAT,expressions,null,null,null,null,null);
		}
		throw new IllegalArgumentException();
	}
	public static StringCompoundExpression createToString(Expression<?>main) {
		return new StringCompoundExpression(main, StringOperator.TOSTR,null,null,null,null,null,null);
	}
	public static StringCompoundExpression createAt(Expression<?> main, Expression<?> position) {
		return new StringCompoundExpression(main, StringOperator.AT,null,null,null,null,null, position);
	}
	
	public static StringCompoundExpression createSubstring(Expression<?> main,Expression<?> offset, Expression<?>length) {
			return new StringCompoundExpression(main,StringOperator.SUBSTR,null, offset,length,null,null,null);
	}
	
	public static StringCompoundExpression createReplace(Expression<?> main,Expression<?> src, Expression<?> dst) {
			return new StringCompoundExpression(main,StringOperator.REPLACE,null,null,null,null, src, dst);
	}
	public StringCompoundExpression(Expression<?> main, StringOperator operator, Expression<?>[]expressions, Expression<?> offset, Expression<?> length, Expression<?> src, Expression<?> dst,Expression<?> position) {
		this.main=main;
		this.src=src;
		this.dst=dst;
		this.operator=operator;
		this.length=length;
		this.expressions=expressions;
		this.offset=offset;
		this.position=position;
		System.out.println("expressions.size "+ expressions.length);
	}

	@Override
	public String evaluate(Valuation values) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
		if(this.main!=null) {
			main.collectFreeVariables(variables);
		}
		if(this.expressions!=null) {
			for(Expression<?> e:expressions) {
				e.collectFreeVariables(variables);
			}
		}
		if(this.dst!=null) this.dst.collectFreeVariables(variables);
	}

	public Expression<?> getMain() {
		return main;
	}

	public Expression<?> [] getExpressions() {
		return expressions;
	}

	public Expression<?> getDst() {
		return dst;
	}

	public StringOperator getOperator() {
		return operator;
	}

	public Expression<?> getOffset() {
		return offset;
	}

	public Expression<?> getLength() {
		return length;
	}
	public Expression<?> getPosition() {
		return position;
	}

	public Expression<?> getSrc() {
		return src;
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

	@Override
	public void print(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub

	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub

	}

}
