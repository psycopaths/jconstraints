package gov.nasa.jpf.constraints.expressions;

public enum RegExOperator implements ExpressionOperator {
  KLEENESTAR("re.*"),
  KLEENEPLUS("re.+"),
  LOOP("re.loop"),
  RANGE("re.range"),
  OPTIONAL("re.opt"),
  STRTORE("str.to.re"),
  ALLCHAR("re.allchar"),
  ALL("re.all"),
  COMPLEMENT("re.comp"),
  NOSTR("re.nostr");

  private final String str;

  RegExOperator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static RegExOperator fromString(String str) {
    switch (str) {
      case "re.loop":
        return LOOP;
      case "re.range":
        return RANGE;
      case "re.*":
        return KLEENESTAR;
      case "re.+":
        return KLEENEPLUS;
      case "re.opt":
        return OPTIONAL;
      case "str.to.re":
        return STRTORE;
      case "re.allchar":
        return ALLCHAR;
      case "re.all":
        return ALL;
      case "re.nostr":
        return NOSTR;
      case "re.comp":
        return COMPLEMENT;
      default:
        return null;
    }
  }
}
