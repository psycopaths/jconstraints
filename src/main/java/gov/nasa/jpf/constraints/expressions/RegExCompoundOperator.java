package gov.nasa.jpf.constraints.expressions;

public enum RegExCompoundOperator implements ExpressionOperator {
  INTERSECTION("re.inter"),
  UNION("re.union"),
  CONCAT("re.++");

  private final String str;

  RegExCompoundOperator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return (" " + str + " ");
  }

  public static RegExCompoundOperator fromString(String str) {
    switch (str) {
      case "re.inter":
        return INTERSECTION;
      case "re.union":
        return UNION;
      case "re.++":
        return CONCAT;
      default:
        return null;
    }
  }
}
