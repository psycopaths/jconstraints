package gov.nasa.jpf.constraints.expressions;

public enum StringIntegerOperator implements ExpressionOperator {
	LENGTH("str.len"),
	INDEXOF("str.indexof"),
	TOINT("str.to.int");
	
	private final String str;
	
	private StringIntegerOperator(String str) {
		this.str=str;
	}
	
	@Override
	  public String toString() {
	    return str;
	  }
	  
	  public static StringIntegerOperator fromString(String str){
	    switch(str){
	      case "str.len": return LENGTH; 
	      case "str.indexof": return INDEXOF;
	      case "str.to.int": return TOINT;
	      default: return null;
	    }
	  }

}
