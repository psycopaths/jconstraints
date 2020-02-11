package gov.nasa.jpf.constraints.expressions;

public enum BooleanOperator implements ExpressionOperator {

	EQ("=="),
	NEQ("!=");
	
	private final String str;
	
	BooleanOperator(String str) {
		this.str=str;
	}
	
	@Override
	  public String toString() {
	    return str;
	  }
	  
	  public static BooleanOperator fromString(String str){
	    switch(str){
	      case "==": return EQ; 
	      case "!=": return NEQ;
	      default: return null;
	    }
	  }
}
