package gov.nasa.jpf.constraints.expressions;

@Deprecated
public enum BooleanOperator implements ExpressionOperator {
  EQ("=="),
  NEQ("!=");

  private final String str;

  BooleanOperator(String str) {
    this.str = str;
  }

  public static BooleanOperator fromString(String str) {
    switch (str) {
      case "==":
        return EQ;
      case "!=":
        return NEQ;
      default:
        return null;
    }
  }

  @Override
  public String toString() {
    return str;
  }
}
