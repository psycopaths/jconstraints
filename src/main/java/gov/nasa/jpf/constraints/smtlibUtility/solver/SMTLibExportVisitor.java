package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExCompoundOperator;
import gov.nasa.jpf.constraints.expressions.RegExOperator;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerOperator;
import gov.nasa.jpf.constraints.expressions.StringOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.math.BigInteger;

public class SMTLibExportVisitor extends AbstractExpressionVisitor<Void, Void> {

  private final SMTLibExportGenContext ctx;

  public SMTLibExportVisitor(SMTLibExportGenContext ctx) {
    this.ctx = ctx;
  }

  public void transform(Expression<?> e) {
    ctx.open("assert");
    defaultVisit(e, null);
    ctx.close();
    ctx.flush();
  }

  @Override
  public <E> Void visit(Variable<E> var, Void v) {
    ctx.appendVar(var);
    return null;
  }

  @Override
  public <E> Void visit(Constant<E> c, Void v) {
    // TODO: add missing data types
    if (BuiltinTypes.SINT32.equals(c.getType())) {
      Integer i = (Integer) c.getValue();
      ctx.append("#x" + String.format("%1$08x", i));
    } else if (BuiltinTypes.SINT8.equals(c.getType())) {
      Byte i = (Byte) c.getValue();
      ctx.append("#x" + String.format("%1$02x", i));
    } else if (BuiltinTypes.UINT16.equals(c.getType())) {
      char i = (Character) c.getValue();
      ctx.append("#x" + String.format("%1$04x", (int) i));
    } else if (BuiltinTypes.INTEGER.equals(c.getType())) {
      BigInteger i = (BigInteger) c.getValue();
      ctx.append(i.toString());
    } else if (BuiltinTypes.STRING.equals(c.getType())) {
      String s = (String) c.getValue();
      ctx.append("\"" + s + "\"");
    } else if (BuiltinTypes.BOOL.equals(c.getType())) {
      ctx.append(c.getValue().toString());
    } else {
      throw new IllegalArgumentException("Unsupported const type: " + c.getType());
    }
    return null;
  }

  @Override
  public Void visit(Negation n, Void v) {
    ctx.open("not");
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(NumericBooleanExpression n, Void v) {
    ctx.open(numComp(n.getComparator(), n.getLeft().getType()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String numComp(NumericComparator nc, Type<?> t) {
    switch (nc) {
      case EQ:
        return "=";
      case NE:
        return "distinct";
      case GE:
        return bvType(t) ? (isSigned(t) ? "bvsge" : "bvuge") : ">=";
      case LE:
        return bvType(t) ? (isSigned(t) ? "bvsle" : "bvule") : "<=";
      case GT:
        return bvType(t) ? (isSigned(t) ? "bvsgt" : "bvugt") : ">";
      case LT:
        return bvType(t) ? (isSigned(t) ? "bvslt" : "bvult") : "<";
      default:
        throw new IllegalArgumentException("Unsupported: " + nc);
    }
  }

  private boolean bvType(Type<?> t) {
    return BuiltinTypes.SINT8.equals(t)
        || BuiltinTypes.SINT16.equals(t)
        || BuiltinTypes.SINT32.equals(t)
        || BuiltinTypes.SINT64.equals(t)
        || BuiltinTypes.UINT16.equals(t);
  }

  @Override
  public Void visit(RegExBooleanExpression n, Void v) {
    ctx.open("str.in.re");
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(StringBooleanExpression n, Void v) {
    ctx.open(stringComp(n.getOperator()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String stringComp(StringBooleanOperator op) {
    switch (op) {
      case EQUALS:
        return "=";
      case CONTAINS:
        return "str.contains";
      case PREFIXOF:
        return "str.prefixof";
      case SUFFIXOF:
        return "str.suffixof";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(StringIntegerExpression n, Void v) {
    ctx.open(stringIntOp(n.getOperator()));
    visit(n.getLeft(), v);
    if (StringIntegerOperator.INDEXOF.equals(n.getOperator())) {
      visit(n.getRight(), v);
      if (n.getOffset() != null) {
        visit(n.getOffset(), v);
      }
    }
    ctx.close();
    return null;
  }

  private String stringIntOp(StringIntegerOperator op) {
    switch (op) {
      case INDEXOF:
        return "str.indexof";
      case LENGTH:
        return "str.len";
      case TOINT:
        // In QF_S this is str.to_int
        return "str.to.int";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(StringCompoundExpression stringCompoundExpression, Void data) {
    ctx.open(stringCompoundOp(stringCompoundExpression.getOperator()));

    for (Expression child : stringCompoundExpression.getChildren()) {
      visit(child, data);
    }
    ctx.close();
    return null;
  }

  private String stringCompoundOp(StringOperator op) {
    switch (op) {
      case CONCAT:
        return "str.++";
      case SUBSTR:
        return "str.substr";
      case AT:
        return "str.at";
      case TOSTR:
        // In QF_S this is str.from_int
        return "int.to.str";
      case REPLACE:
        return "str.replace";
      case TOLOWERCASE:
        return "str.lower";
      case TOUPPERCASE:
        return "str.upper";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(RegexCompoundExpression n, Void data) {
    ctx.open(regexCompoundOp(n.getOperator()));
    for (Expression child : n.getChildren()) {
      visit(child, data);
    }
    ctx.close();
    return null;
  }

  private String regexCompoundOp(RegExCompoundOperator op) {
    switch (op) {
      case INTERSECTION:
        return "re.inter";
      case UNION:
        return "re.union";
      case CONCAT:
        return "re.++";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  private String regexOp(RegExOperator op) {
    switch (op) {
      case KLEENESTAR:
        return "re.*";
      case KLEENEPLUS:
        return "re.+";
      case LOOP:
        return "re.loop";
      case RANGE:
        return "re.range";
      case OPTIONAL:
        return "re.opt";
      case STRTORE:
        return "str.to_re";
      case ALLCHAR:
        return "re.allchar";
      case ALL:
        return "re.all";
      case COMPLEMENT:
        return "re.comp";
      case NOSTR:
        return "re.none";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public Void visit(RegexOperatorExpression n, Void data) {
    String operator = regexOp(n.getOperator());
    ctx.open(operator);
    switch (n.getOperator()) {
      case KLEENESTAR:
        visit(n.getLeft(), data);
        break;
      case KLEENEPLUS:
        visit(n.getLeft(), data);
        break;
      case LOOP:
        throw new UnsupportedOperationException("");
      case RANGE:
        ctx.append("\"" + n.getCh1() + "\"");
        ctx.append("\"" + n.getCh2() + "\"");
        break;
      case OPTIONAL:
        visit(n.getLeft(), data);
        break;
      case STRTORE:
        ctx.append("\"" + n.getS() + "\"");
        break;
      case ALLCHAR:
        break;
      case ALL:
        throw new UnsupportedOperationException();
      case COMPLEMENT:
        visit(n.getLeft(), data);
        break;
      case NOSTR:
        break;
      default:
        throw new UnsupportedOperationException();
    }
    ctx.close();
    return null;
  }

  @Override
  public <F, E> Void visit(CastExpression<F, E> cast, Void v) {
    if (BuiltinTypes.INTEGER.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      return castIntegerSINTX(cast, 32);
    } else if (BuiltinTypes.INTEGER.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT8.equals(cast.getType())) {
      return castIntegerSINTX(cast, 8);
    } else if (BuiltinTypes.SINT32.equals(cast.getCasted().getType())
        && BuiltinTypes.INTEGER.equals(cast.getType())) {
      return castSINTXInteger(cast);
    } else if (BuiltinTypes.SINT8.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      return castSignExtend(cast, 24);
    } else if (BuiltinTypes.SINT8.equals(cast.getCasted().getType())
        && BuiltinTypes.UINT16.equals(cast.getType())) {
      // This is a byte to char cast in the jConstraints semantic:
      // https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.1.4
      return castSignExtend(cast, 8);
    } else if (BuiltinTypes.UINT16.equals(cast.getCasted().getType())
        && BuiltinTypes.SINT32.equals(cast.getType())) {
      // This is a char to byte cast in the jConstraints semantic:
      // https://docs.oracle.com/javase/specs/jls/se8/html/jls-5.html#jls-5.1.2
      return castZeroExtend(cast, 16);
    } else {
      throw new UnsupportedOperationException(
          "casting is not supported by SMTLib support currently");
    }
  }

  @Override
  public <E> Void visit(NumericCompound<E> n, Void v) {
    ctx.open(numOp(n.getOperator(), n.getType()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String numOp(NumericOperator op, Type t) {
    switch (op) {
      case DIV:
        return bvType(t)
            ? (isSigned(t) ? "bvsdiv" : "bvudiv")
            : (BuiltinTypes.REAL.equals(t) ? "/" : "div");
      case MINUS:
        return bvType(t) ? "bvsub" : "-";
      case MUL:
        return bvType(t) ? "bvmul" : "*";
      case PLUS:
        return bvType(t) ? "bvadd" : "+";
      case REM:
        return bvType(t) ? (isSigned(t) ? "bvsrem" : "bvurem") : "mod";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  private boolean isSigned(Type t) {
    if (t instanceof BVIntegerType) {
      BVIntegerType casted = (BVIntegerType) t;
      return casted.isSigned();
    }
    throw new IllegalArgumentException("The type must be a BV type");
  }

  @Override
  public Void visit(PropositionalCompound n, Void v) {
    ctx.open(logicOp(n.getOperator()));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String logicOp(LogicalOperator op) {
    switch (op) {
      case AND:
        return "and";
      case IMPLY:
        return "=>";
      case OR:
        return "or";
      case EQUIV:
        return "=";
      case XOR:
        return "xor";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public <E> Void visit(IfThenElse<E> n, Void v) {
    ctx.open("ite");
    visit(n.getIf(), v);
    visit(n.getThen(), v);
    visit(n.getElse(), v);
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(UnaryMinus<E> n, Void v) {
    if (n.getNegated().getType() instanceof BVIntegerType) {
      ctx.open("bvneg");
    } else {
      ctx.open("-");
    }
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(BitvectorExpression<E> n, Void v) {
    ctx.open(bvOp((n.getOperator())));
    visit(n.getLeft(), v);
    visit(n.getRight(), v);
    ctx.close();
    return null;
  }

  private String bvOp(BitvectorOperator op) {
    switch (op) {
      case AND:
        return "bvand";
      case OR:
        return "bvor";
      case XOR:
        return "bvxor";
      case SHIFTL:
        return "bvshl";
      case SHIFTR:
        return "bvashr";
      case SHIFTUR:
        return "bvlshr";
      default:
        throw new IllegalArgumentException("Unsupported: " + op);
    }
  }

  @Override
  public <E> Void visit(BitvectorNegation<E> n, Void v) {
    ctx.open("bvnot");
    visit(n.getNegated(), v);
    ctx.close();
    return null;
  }

  @Override
  public Void visit(QuantifierExpression q, Void v) {
    // TODO: this is untested!
    ctx.open("" + q.getQuantifier());
    for (Variable<?> var : q.getBoundVariables()) {
      ctx.appendLocalVarDecl(var);
    }
    visit(q.getBody());
    ctx.close();
    return null;
  }

  @Override
  public <E> Void visit(FunctionExpression<E> f, Void data) {
    throw new UnsupportedOperationException("not implemented yet.");
    // TODO: implement support for function expressions
    // return null;
  }

  @Override
  public Void visit(LetExpression n, Void v) {
    ctx.open("let");
    ctx.open("");
    for (Variable<?> var : n.getParameters()) {
      ctx.registerLocalSymbol(var);
      ctx.open(var.getName());
      // FIXME: can this be null?
      visit(n.getParameterValues().get(var), v);
      ctx.close();
    }
    ctx.close();
    visit(n.getMainValue(), v);
    ctx.close();
    return null;
  }

  @Override
  protected <E> Void defaultVisit(Expression<E> expression, Void v) {
    visit(expression, v);
    return null;
  }

  /* Below this line should only be private casting methods
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*/
  private Void castIntegerSINTX(CastExpression cast, int bits) {
    ctx.open("ite");
    ctx.open("<");
    visit(cast.getCasted());
    visit(Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0)));
    ctx.close();
    ctx.open("bvneg");
    ctx.open(String.format("(_ nat2bv %d)", bits));
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    ctx.open(String.format("(_ nat2bv %d)", bits));
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    return null;
  }

  private Void castSINTXInteger(CastExpression cast) {
    ctx.open("ite");
    ctx.open("bvslt");
    visit(cast.getCasted());
    visit(Constant.create(BuiltinTypes.SINT32, 0));
    ctx.close();
    ctx.open("-");
    ctx.open("bv2nat");
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    ctx.open("bv2nat");
    visit(cast.getCasted());
    ctx.close();
    ctx.close();
    return null;
  }

  private Void castSignExtend(CastExpression cast, int bits) {
    ctx.open(String.format("(_ sign_extend %d)", bits));
    visit(cast.getCasted());
    ctx.close();
    return null;
  }

  private Void castZeroExtend(CastExpression cast, int bits) {
    ctx.open(String.format("(_ zero_extend %d)", bits));
    visit(cast.getCasted());
    ctx.close();
    return null;
  }
}
