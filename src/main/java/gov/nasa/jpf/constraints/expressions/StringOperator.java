package gov.nasa.jpf.constraints.expressions;

public enum StringOperator implements ExpressionOperator {
	CONCAT("str.++"),
	SUBSTR("str.substr"),
	AT("str.at"),
	TOSTR("int.to.str"),
	REPLACE("str.replace");
	
	private final String str;
	
	private StringOperator(String str) {
		this.str=str;
	}
	
	@Override
	  public String toString() {
	    return str;
	  }
	  
	  public static StringOperator fromString(String str){
	    switch(str){
	      case "str.++": return CONCAT; 
	      case "str.substr": return SUBSTR;
	      case "str.at": return AT;
	      case "int.to.str": return TOSTR;
	      case "str.replace": return REPLACE;
	      default: return null;
	    }
	  }
}
