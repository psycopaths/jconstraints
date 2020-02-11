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
	private final char ch1;
	private final char ch2;
	private final String s;
	
	private RegexOperatorExpression(Expression<?> left, RegExOperator operator, int low, int high,char ch1,char ch2,String s) {
		this.left=left;
		this.operator=operator;
		this.low = low;
		this.high = high;
		this.ch1 = ch1;
		this.ch2 = ch2;
		this.s=s;
	}

	public static RegexOperatorExpression createLoop(Expression<?>left,int low) {
		return new RegexOperatorExpression(left,RegExOperator.LOOP, low,low,'0','0',"");
	}
	public static RegexOperatorExpression createLoop(Expression<?>left,int low, int high) {
		return new RegexOperatorExpression(left,RegExOperator.LOOP, low,high,'0','0',"");
	}
	public static RegexOperatorExpression createKleeneStar(Expression<?> left) {
		return new RegexOperatorExpression(left,RegExOperator.KLEENESTAR,0,0,'0','0',"");
	}
	public static RegexOperatorExpression createKleenePlus(Expression<?> left) {
		return new RegexOperatorExpression(left,RegExOperator.KLEENEPLUS,0,0,'0','0',"");
	}
	public static RegexOperatorExpression createOptional(Expression<?> left) {
		return new RegexOperatorExpression(left,RegExOperator.OPTIONAL,0,0,'0','0',"");
	}
	public static RegexOperatorExpression createRange(char ch1, char ch2) {
		return new RegexOperatorExpression(null,RegExOperator.RANGE,0,0,ch1,ch2,"");
	}
	public static RegexOperatorExpression createStrToRe(String s) {
		return new RegexOperatorExpression(null,RegExOperator.STRTORE,0,0,'0','0',s);
	}
	public static RegexOperatorExpression createAllChar() {
		return new RegexOperatorExpression(null,RegExOperator.ALLCHAR,0,0,'0','0',"");
	}
	public static RegexOperatorExpression createNoChar() {
		return new RegexOperatorExpression(null,RegExOperator.NOCHAR,0,0,'0','0',"");
	}
	public Expression<?> getLeft() {
		return left;
	}
	
	
	public int getLow() {
		return low;
	}

	public int getHigh() {
		return high;
	}

	public char getCh1() {
		return ch1;
	}

	public char getCh2() {
		return ch2;
	}
	
	
	
	public String getS() {
		return s;
	}

	public RegExOperator getOperator() {
		return operator;
	}
	@Override
	public String evaluate(Valuation values) {
		switch (operator) {
		case ALLCHAR:
			return evaluateAllChar(values);
		case KLEENEPLUS:
			return evaluateKleenePlus(values);
		case KLEENESTAR:
			return evaluateKleeneStar(values);
		case LOOP:
			return evaluateLoop(values);
		case NOCHAR:
			return evaluateNoChar(values);
		case OPTIONAL:
			return evaluateOptional(values);
		case RANGE:
			evaluateRange(values);
		case STRTORE:
			return evaluateStrToRe(values);
		default:
			throw new IllegalArgumentException();		
		}	
//		throw new UnsupportedOperationException(this.getClass().getName() + ": evaluate is not Implemented");
	}

	private String evaluateStrToRe(Valuation values) {
		return s;
		
	}

	private String evaluateRange(Valuation values) {
		return "[" +ch1 + "-" +ch2 +"]";
	}

	private String evaluateOptional(Valuation values) {
		String regex = (String) left.evaluate(values);
		String result = "(" + regex +")?";
		return result;
		
	}

	private String evaluateNoChar(Valuation values) {
		return "(^.*)";
		
	}

	private String evaluateLoop(Valuation values) {
		String regex = (String)left.evaluate(values);
		return "(" + regex +"){"+low +"," +high +"}";
	}

	private String evaluateKleeneStar(Valuation values) {
		String regex = (String)left.evaluate(values);
		return "(" + regex +")*";
		
	}

	private String evaluateKleenePlus(Valuation values) {
		String regex = (String)left.evaluate(values);
		return "(" + regex +")+";
		
	}

	private String evaluateAllChar(Valuation values) {
		return "(.*)";
		
	}

	@Override
	public void collectFreeVariables(Collection<? super Variable<?>> variables) {
	    if(this.left!=null) {
	    	this.left.collectFreeVariables(variables);
	    }
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
//		a.append('(');
//		left.print(a, flags);
//		a.append(operator.toString());
//		a.append(')');
		
	}

	@Override
	public void printMalformedExpression(Appendable a, int flags) throws IOException {
		// TODO Auto-generated method stub
		
	}
}
