package gov.nasa.jpf.constraints.expressions;

public enum StringOperator implements ExpressionOperator {
	CONCAT("str.++"),
	SUBSTR("str.substr"),
	AT("str.at"),
	TOSTR("int.to.str"),
	FROMSTR("str.from_int"),
	REPLACE("str.replace"),
	TOLOWERCASE("str.lower"),
	TOUPPERCASE("str.upper");

	private final String str;

	private StringOperator(String str) {
		this.str = str;
	}

	@Override
	public String toString() {
		return str;
	}

	public static StringOperator fromString(String str) {
		switch (str) {
			case "str.++":
				return CONCAT;
			case "str.substr":
				return SUBSTR;
			case "str.at":
				return AT;
			case "int.to.str":
				return TOSTR;
			case "str.replace":
				return REPLACE;
			case "str.lower":
				return TOLOWERCASE;
			case "str.upper":
				return TOUPPERCASE;
			default:
				return null;
		}
	}
}
