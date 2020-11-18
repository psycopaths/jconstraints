package gov.nasa.jpf.constraints.expressions;

public enum RegExBooleanOperator implements ExpressionOperator {
  STRINRE("str.in.re");

  private final String str;

  RegExBooleanOperator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static RegExBooleanOperator fromString(String str) {
    switch (str) {
      case "str.in.re":
        return STRINRE;
      default:
        return null;
    }
  }
}
