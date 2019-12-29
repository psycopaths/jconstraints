package gov.nasa.jpf.constraints.expressions;

public enum RegExCompoundOperator implements ExpressionOperator {

	INTERSECTION("intersection"),
	UNION("union"),
	CONCAT("concat");
	
	private final String str;

	RegExCompoundOperator(String str) {
	    this.str = str;
	  }

	  @Override
	  public String toString() {
	    return (" "+ str + " ");
	  }
	  
	  public static RegExCompoundOperator fromString(String str){
	    switch(str){
	      case "intersection": return INTERSECTION;
	      case "union": return UNION;
	      case "concat": return CONCAT;
	      default: return null;
	    }
	  }
}
