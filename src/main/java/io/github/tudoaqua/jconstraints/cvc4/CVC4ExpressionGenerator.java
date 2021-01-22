/**
 * Copyright 2020 TU Dortmund, Nils Schmidt und Malte Mues
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.github.tudoaqua.jconstraints.cvc4;

import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.BitVectorExtract;
import edu.stanford.CVC4.BitVectorSignExtend;
import edu.stanford.CVC4.BitVectorZeroExtend;
import edu.stanford.CVC4.CVC4String;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.FloatingPoint;
import edu.stanford.CVC4.FloatingPointSize;
import edu.stanford.CVC4.FloatingPointToFPFloatingPoint;
import edu.stanford.CVC4.FloatingPointToFPSignedBitVector;
import edu.stanford.CVC4.FloatingPointToSBV;
import edu.stanford.CVC4.IntToBitVector;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.RoundingMode;
import edu.stanford.CVC4.vectorExpr;
import edu.stanford.CVC4.vectorType;
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
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerOperator;
import gov.nasa.jpf.constraints.expressions.StringOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.ConcreteBVIntegerType;
import gov.nasa.jpf.constraints.types.ConcreteFloatingPointType;
import gov.nasa.jpf.constraints.types.NamedSort;
import gov.nasa.jpf.constraints.types.Type;
import io.github.tudoaqua.jconstraints.cvc4.exception.CVC4ConversionException;
import java.util.HashMap;
import org.apache.commons.math3.fraction.BigFraction;

public class CVC4ExpressionGenerator extends AbstractExpressionVisitor<Expr, Expr> {

  private final ExprManager em;
  private HashMap<Variable, Expr> vars;
  private HashMap<String, edu.stanford.CVC4.Type> declaredTypes;
  private HashMap<Function, Expr> declaredFunctions;

  private FloatingPointSize doubleSize = new FloatingPointSize(11, 53);
  private FloatingPointSize floatSize = new FloatingPointSize(8, 24);

  private Expr defaultRoundingMode;

  public CVC4ExpressionGenerator(ExprManager emT) {
    vars = new HashMap<>();
    this.em = emT;
    declaredTypes = new HashMap<>();
    declaredFunctions = new HashMap<>();
    defaultRoundingMode = em.mkConst(RoundingMode.roundNearestTiesToEven);
  }

  public CVC4ExpressionGenerator(ExprManager emT, HashMap<Variable, Expr> vars) {
    this(emT);
    this.vars = vars;
  }

  public Expr generateExpression(Expression<Boolean> expression) {
    Expr expr = visit(expression);
    return expr;
  }

  @Override
  public <E> Expr visit(Variable<E> v, Expr data) {
    Type<E> t = v.getType();
    if (vars.containsKey(v)) {
      return vars.get(v);
    } else {
      Expr var = em.mkVar(v.getName(), typeMapjConstraintsCVC4(v.getType()));
      vars.put(v, var);
      return var;
    }
  }

  @Override
  public <E> Expr visit(Constant<E> c, Expr data) {
    if (c.getType().equals(BuiltinTypes.BOOL)) {
      return em.mkConst((Boolean) c.getValue());
    } else if (c.getType().equals(BuiltinTypes.REAL)) {
      BigFraction bf = (BigFraction) c.getValue();
      return em.mkConst(new Rational(bf.getNumerator(), bf.getDenominator()));
    } else if (c.getType().equals(BuiltinTypes.SINT32)) {
      Constant<java.lang.Integer> intConst = (Constant<java.lang.Integer>) c;
      return em.mkConst(new BitVector(32, intConst.getValue()));
    } else if (c.getType().equals(BuiltinTypes.SINT64)) {
      Constant<Long> longConst = (Constant<Long>) c;
      return em.mkConst(new BitVector(64, longConst.getValue()));
    } else if (c.getType().equals(BuiltinTypes.INTEGER)) {
      return em.mkConst(new Rational(c.getValue().toString()));
    } else if (c.getType().equals(BuiltinTypes.DOUBLE)) {
      double value = (Double) c.getValue();
      if (value == 0.0) {
        return em.mkConst(FloatingPoint.makeZero(doubleSize, true));
      }
      long longValue = Double.doubleToLongBits(value);
      String bitvector = Long.toBinaryString(longValue);
      for (int i = 0; i < Long.numberOfLeadingZeros(longValue); ++i) {
        bitvector = "0" + bitvector;
      }
      BitVector r = new BitVector(bitvector);
      return em.mkConst(new FloatingPoint(doubleSize.exponent(), doubleSize.significand(), r));
    } else if (c.getType().equals(BuiltinTypes.FLOAT)) {
      float value = (Float) c.getValue();
      if (value == 0.0f) {
        return em.mkConst(FloatingPoint.makeZero(floatSize, true));
      }
      int intValue = Float.floatToIntBits(value);
      String bitvector = Integer.toBinaryString(intValue);
      for (int i = 0; i < Integer.numberOfLeadingZeros(intValue); ++i) {
        bitvector = "0" + bitvector;
      }
      BitVector r = new BitVector(bitvector);
      return em.mkConst(new FloatingPoint(floatSize.exponent(), floatSize.significand(), r));
    } else if (c.getType().equals(BuiltinTypes.STRING)) {
      return em.mkConst(new CVC4String(c.getValue().toString()));
    } else {
      throw new UnsupportedOperationException(
          "Cannot convert Constant: " + c.getType() + "with value: " + c.getValue());
    }
  }

  @Override
  public Expr visit(Negation n, Expr data) {
    Expr containted = visit(n.getNegated(), data);
    return containted.notExpr();
  }

  @Override
  public Expr visit(NumericBooleanExpression n, Expr data) {
    Expr left = visit(n.getLeft(), data);
    Expr right = visit(n.getRight(), data);

    boolean bvTypes = isBVType(n.getLeft(), n.getRight());
    boolean fpTypes = isFPType(n.getLeft(), n.getRight());
    boolean signed = isSigned(n.getLeft(), n.getRight());

    Kind kComperator = convertNumericComparator(n.getComparator(), bvTypes, fpTypes, signed);
    if (fpTypes) {
      if (kComperator == null && n.getComparator().equals(NumericComparator.NE)) {
        Expr equals = em.mkExpr(Kind.FLOATINGPOINT_EQ, left, right);
        return em.mkExpr(Kind.NOT, equals);
      }
    }

    return em.mkExpr(kComperator, left, right);
  }

  @Override
  public <E> Expr visit(NumericCompound<E> n, Expr data) {
    Expr left = visit(n.getLeft(), data);
    Expr right = visit(n.getRight(), data);

    boolean bvTypes = isBVType(n.getLeft(), n.getRight());
    boolean fpTypes = isFPType(n.getLeft(), n.getRight());
    boolean signed = isSigned(n.getLeft(), n.getRight());

    Kind kOperator = convertNumericOperator(n.getOperator(), bvTypes, fpTypes, signed);

    if (fpTypes) {
      return em.mkExpr(kOperator, defaultRoundingMode, left, right);
    } else {
      return em.mkExpr(kOperator, left, right);
    }
  }

  @Override
  public Expr visit(PropositionalCompound n, Expr data) {
    Expr left = visit(n.getLeft(), data);
    Expr right = visit(n.getRight(), data);
    Expr all = null;
    switch (n.getOperator()) {
      case AND:
        all = em.mkExpr(Kind.AND, left, right);
        break;
      case OR:
        all = em.mkExpr(Kind.OR, left, right);
        break;
      case XOR:
        all = em.mkExpr(Kind.XOR, left, right);
        break;
      case EQUIV:
        all = em.mkExpr(Kind.EQUAL, left, right);
        break;
      case IMPLY:
        all = em.mkExpr(Kind.IMPLIES, left, right);
        break;
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + n.toString());
    }
    return all;
  }

  @Override
  public <E> Expr visit(UnaryMinus<E> n, Expr data) {
    Expr negated = visit(n.getNegated());
    if (n.getNegated().getType() instanceof ConcreteBVIntegerType) {
      return em.mkExpr(Kind.BITVECTOR_NEG, negated);
    } else if (n.getNegated().getType() instanceof ConcreteFloatingPointType) {
      return em.mkExpr(Kind.FLOATINGPOINT_NEG, negated);
    } else {
      return em.mkExpr(Kind.UMINUS, negated);
    }
  }

  public Expr visit(Function f, Expr data) {
    if (declaredFunctions.containsKey(f)) {
      return declaredFunctions.get(f);
    }
    vectorType functionTypes = new vectorType(em);
    for (Type t : f.getParamTypes()) {
      functionTypes.add(typeMapjConstraintsCVC4(t));
    }
    functionTypes.add(typeMapjConstraintsCVC4(f.getReturnType()));
    edu.stanford.CVC4.Type fType = em.mkFunctionType(functionTypes);
    Expr function = em.mkVar(f.getName(), fType);
    declaredFunctions.put(f, function);
    return function;
  }

  @Override
  public <E> Expr visit(FunctionExpression<E> f, Expr data) {
    Expr function = visit(f.getFunction(), data);
    vectorExpr args = new vectorExpr(em);
    for (Expression e : f.getArgs()) {
      args.add(visit(e, data));
    }
    return em.mkExpr(Kind.APPLY_UF, function, args);
  }

  @Override
  public <F, E> Expr visit(CastExpression<F, E> cast, Expr data) {
    Type t = cast.getType();
    if (cast.getType().equals(BuiltinTypes.SINT32)
        && cast.getCasted().getType().equals(BuiltinTypes.INTEGER)) {
      Expr conversion = em.mkConst(new IntToBitVector(32));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT32)
        && cast.getCasted().getType().equals(BuiltinTypes.UINT16)) {
      Expr conversion = em.mkConst(new BitVectorZeroExtend(16));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT32)
        && cast.getCasted().getType().equals(BuiltinTypes.SINT16)) {
      Expr conversion = em.mkConst(new BitVectorSignExtend(16));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT32)
        && cast.getCasted().getType().equals(BuiltinTypes.SINT8)) {
      Expr conversion = em.mkConst(new BitVectorSignExtend(24));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT32)
        && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE)
            || cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op = em.mkConst(new FloatingPointToSBV(32));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getType().equals(BuiltinTypes.SINT64)
        && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE)
            || cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op = em.mkConst(new FloatingPointToSBV(64));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getType().equals(BuiltinTypes.SINT64)
        && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
      Expr conversion = em.mkConst(new BitVectorSignExtend(32));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.UINT16)
        && cast.getCasted().getType() instanceof BVIntegerType) {
      Expr conversion = em.mkConst(new BitVectorExtract(15, 0));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT16)
        && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
      Expr conversion = em.mkConst(new BitVectorExtract(15, 0));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.SINT8)
        && cast.getCasted().getType() instanceof BVIntegerType) {
      Expr conversion = em.mkConst(new BitVectorExtract(7, 0));
      return em.mkExpr(conversion, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.INTEGER)
        && cast.getCasted().getType() instanceof BVIntegerType) {
      return em.mkExpr(Kind.BITVECTOR_TO_NAT, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.INTEGER)
        && cast.getCasted().getType().equals(BuiltinTypes.REAL)) {
      return em.mkExpr(Kind.TO_INTEGER, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.REAL)
        && cast.getCasted().getType().equals(BuiltinTypes.INTEGER)) {
      return em.mkExpr(Kind.TO_REAL, visit(cast.getCasted(), data));
    } else if (cast.getType().equals(BuiltinTypes.DOUBLE)
        && (cast.getCasted().getType().equals(BuiltinTypes.SINT32)
        || cast.getCasted().getType().equals(BuiltinTypes.SINT64))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op =
          em.mkConst(
              new FloatingPointToFPSignedBitVector(
                  doubleSize.exponent(), doubleSize.significand()));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getType().equals(BuiltinTypes.DOUBLE)
        && (cast.getCasted().getType().equals(BuiltinTypes.FLOAT))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op =
          em.mkConst(
              new FloatingPointToFPFloatingPoint(doubleSize.exponent(), doubleSize.significand()));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getType().equals(BuiltinTypes.FLOAT)
        && (cast.getCasted().getType().equals(BuiltinTypes.DOUBLE))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op =
          em.mkConst(
              new FloatingPointToFPFloatingPoint(floatSize.exponent(), floatSize.significand()));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getType().equals(BuiltinTypes.FLOAT)
        && (cast.getCasted().getType().equals(BuiltinTypes.SINT32)
        || cast.getCasted().getType().equals(BuiltinTypes.SINT64))) {
      Expr toCast = visit(cast.getCasted(), data);
      Expr op =
          em.mkConst(
              new FloatingPointToFPSignedBitVector(floatSize.exponent(), floatSize.significand()));
      return em.mkExpr(op, defaultRoundingMode, toCast);
    } else if (cast.getCasted() instanceof Constant) {
      if (cast.getType().equals(BuiltinTypes.INTEGER)) {
        return em.mkConst(new Rational(((Constant<F>) cast.getCasted()).getValue().toString()));
      }
    }
    throw new UnsupportedOperationException(
        String.format(
            "Cannot cast: %s to %s",
            cast.getCasted().getType().getName(), cast.getType().getName()));
  }

  @Override
  public <E> Expr visit(IfThenElse<E> n, Expr data) {
    Expr condition = visit(n.getIf(), data);
    Expr ifPart = visit(n.getThen(), data);
    Expr elsePart = visit(n.getElse(), data);

    return em.mkExpr(Kind.ITE, condition, ifPart, elsePart);
  }

  @Override
  public <E> Expr visit(BitvectorExpression<E> bv, Expr data) {
    Expr left = visit(bv.getLeft(), data);
    Expr right = visit(bv.getRight(), data);
    Kind bvOperator = convertBVOperator(bv.getOperator());
    return em.mkExpr(bvOperator, left, right);
  }

  @Override
  public Expr visit(LetExpression let, Expr data) {
    Expression e = let.flattenLetExpression();
    return visit(e, data);
  }

  @Override
  public Expr visit(StringBooleanExpression n, Expr data) {
    vectorExpr exprs = new vectorExpr(em);
    for (Expression child : n.getChildren()) {
      exprs.add(visit(child, data));
    }
    Kind operator = convertStringBooleanOpeartor(n.getOperator());
    return em.mkExpr(operator, exprs);
  }

  @Override
  public Expr visit(StringIntegerExpression n, Expr data) {
    vectorExpr exprs = new vectorExpr(em);
    for (Expression child : n.getChildren()) {
      exprs.add(visit(child, data));
    }
    Kind operator = convertStringIntegerOpeartor(n.getOperator());
    return em.mkExpr(operator, exprs);
  }

  @Override
  public Expr visit(StringCompoundExpression n, Expr data) {
    vectorExpr exprs = new vectorExpr(em);
    for (Expression child : n.getChildren()) {
      exprs.add(visit(child, data));
    }
    Kind operator = convertStringCompundOpeator(n.getOperator());
    return em.mkExpr(operator, exprs);
  }

  @Override
  public Expr visit(RegExBooleanExpression n, Expr data) {
    Expr left = visit(n.getLeft());
    Expr right = visit(n.getRight());
    return em.mkExpr(Kind.STRING_IN_REGEXP, left, right);
  }

  @Override
  public Expr visit(RegexCompoundExpression n, Expr data) {
    Expr left = visit(n.getLeft());
    Expr right = visit(n.getRight());
    switch (n.getOperator()) {
      case CONCAT:
        return em.mkExpr(Kind.REGEXP_CONCAT, left, right);
      case UNION:
        return em.mkExpr(Kind.REGEXP_UNION, left, right);
      case INTERSECTION:
        return em.mkExpr(Kind.REGEXP_INTER, left, right);
      default:
        throw new UnsupportedOperationException("Don't know Operator: " + n.getOperator());
    }
  }

  @Override
  public Expr visit(RegexOperatorExpression n, Expr data) {
    switch (n.getOperator()) {
      case KLEENESTAR:
        Expr left = visit(n.getLeft(), data);
        return em.mkExpr(Kind.REGEXP_STAR, left);
      case KLEENEPLUS:
        left = visit(n.getLeft(), data);
        return em.mkExpr(Kind.REGEXP_PLUS, left);
      case LOOP:
        throw new UnsupportedOperationException();
      case RANGE:
        Expr from = em.mkConst(new CVC4String(Character.toString(n.getCh1())));
        Expr to = em.mkConst(new CVC4String(Character.toString(n.getCh2())));
        return em.mkExpr(Kind.REGEXP_RANGE, from, to);
      case OPTIONAL:
        left = visit(n.getLeft(), data);
        return em.mkExpr(Kind.REGEXP_OPT, left);
      case STRTORE:
        left = em.mkConst(new CVC4String(n.getS()));
        return em.mkExpr(Kind.STRING_TO_REGEXP, left);
      case ALLCHAR:
        return em.mkConst(Kind.REGEXP_SIGMA);
      case ALL:
        throw new UnsupportedOperationException();
      case COMPLEMENT:
        left = visit(n.getLeft(), data);
        return em.mkExpr(Kind.REGEXP_COMPLEMENT, left);
      case NOSTR:
        return em.mkConst(Kind.REGEXP_EMPTY);
      default:
        throw new UnsupportedOperationException();
    }
  }

  @Override
  public Expr visit(QuantifierExpression q, Expr data) {
    vectorExpr args = new vectorExpr(em);
    vectorExpr vars = new vectorExpr(em);
    for (Variable v : q.getBoundVariables()) {
      vars.add(em.mkBoundVar(v.getName(), typeMapjConstraintsCVC4(v.getType())));
    }
    args.add(em.mkExpr(Kind.BOUND_VAR_LIST, vars));
    Expr body = visit(q.getBody(), data);
    args.add(body);

    switch (q.getQuantifier()) {
      case EXISTS:
        return em.mkExpr(Kind.EXISTS, args);
      case FORALL:
        return em.mkExpr(Kind.FORALL, args);
      default:
        throw new IllegalArgumentException("There are only two quantifiers");
    }
  }

  @Override
  public <E> Expr visit(BitvectorNegation<E> n, Expr data) {
    Expr child = visit(n.getNegated(), data);
    return em.mkExpr(Kind.BITVECTOR_NEG, child);
  }

  public HashMap<Variable, Expr> getVars() {
    return new HashMap<>(vars);
  }

  public void clearVars() {
    vars.clear();
  }

  private edu.stanford.CVC4.Type typeMapjConstraintsCVC4(Type type) {
    if (type instanceof BuiltinTypes.RealType) {
      return em.realType();
    } else if (type instanceof BuiltinTypes.BoolType) {
      return em.booleanType();
    } else if (type instanceof BuiltinTypes.BigDecimalType) {
      BuiltinTypes.BigDecimalType decimal = (BuiltinTypes.BigDecimalType) type;
      return em.realType();
    } else if (type instanceof BuiltinTypes.DoubleType) {
      return em.mkFloatingPointType(doubleSize.exponent(), doubleSize.significand());
    } else if (type instanceof BuiltinTypes.FloatType) {
      return em.mkFloatingPointType(floatSize.exponent(), floatSize.significand());
    } else if (type instanceof BuiltinTypes.BigIntegerType) {
      return em.integerType();
    } else if (type instanceof BVIntegerType) {
      return em.mkBitVectorType(((BVIntegerType<?>) type).getNumBits());
    } else if (type.equals(BuiltinTypes.STRING)) {
      return em.stringType();
    } else if (type instanceof NamedSort) {
      if (declaredTypes.containsKey(type.getName())) {
        return declaredTypes.get(type.getName());
      } else {
        edu.stanford.CVC4.Type t = em.mkSort(type.getName());
        declaredTypes.put(type.getName(), t);
        return t;
      }

    } else {
      throw new CVC4ConversionException("Cannot convert Type: " + type.getName());
    }
  }

  private Kind convertStringBooleanOpeartor(StringBooleanOperator operator) {
    switch (operator) {
      case EQUALS:
        return Kind.EQUAL;
      case CONTAINS:
        return Kind.STRING_STRCTN;
      case PREFIXOF:
        return Kind.STRING_PREFIX;
      case SUFFIXOF:
        return Kind.STRING_SUFFIX;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert the Operator: " + operator.toString());
    }
  }

  private Kind convertStringIntegerOpeartor(StringIntegerOperator operator) {
    switch (operator) {
      case INDEXOF:
        return Kind.STRING_STRIDOF;
      case TOINT:
        return Kind.STRING_STOI;
      case LENGTH:
        return Kind.STRING_LENGTH;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert the Operator: " + operator.toString());
    }
  }

  private Kind convertStringCompundOpeator(StringOperator operator) {
    switch (operator) {
      case AT:
        return Kind.STRING_CHARAT;
      case TOSTR:
        return Kind.STRING_ITOS;
      case CONCAT:
        return Kind.STRING_CONCAT;
      case SUBSTR:
        return Kind.STRING_SUBSTR;
      case REPLACE:
        return Kind.STRING_STRREPL;
      case TOLOWERCASE:
        return Kind.STRING_TOLOWER;
      case TOUPPERCASE:
        return Kind.STRING_TOUPPER;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert StringCompundOperator: " + operator.toString());
    }
  }

  private Kind convertBVOperator(BitvectorOperator operator) {
    switch (operator) {
      case AND:
        return Kind.BITVECTOR_AND;
      case OR:
        return Kind.BITVECTOR_OR;
      case XOR:
        return Kind.BITVECTOR_XOR;
      case SHIFTL:
        return Kind.BITVECTOR_SHL;
      case SHIFTR:
        return Kind.BITVECTOR_LSHR;
      case SHIFTUR:
        return Kind.BITVECTOR_ASHR;
      default:
        throw new UnsupportedOperationException(
            "Cannot convert BitvectorOperator: " + operator.toString() + " yet.");
    }
  }

  private Kind convertNumericComparator(
      NumericComparator comparator, boolean byTypes, boolean fpTypes, boolean signed) {
    if (byTypes) {
      return convertNumericComparatorBV(comparator, signed);
    } else if (fpTypes) {
      return ConvertNumericComperatorFP(comparator);
    } else {
      return convertNumericComparatorNBV(comparator);
    }
  }

  private Kind ConvertNumericComperatorFP(NumericComparator comparator) {
    switch (comparator) {
      case EQ:
        return Kind.FLOATINGPOINT_EQ;
      case NE:
        return null;
      case LT:
        return Kind.FLOATINGPOINT_LT;
      case LE:
        return Kind.FLOATINGPOINT_LEQ;
      case GT:
        return Kind.FLOATINGPOINT_GT;
      case GE:
        return Kind.FLOATINGPOINT_GEQ;
      default:
        throw new UnsupportedOperationException("Cannot resovle comparator to FP type");
    }
  }

  private Kind convertNumericComparatorNBV(NumericComparator cmp) {
    switch (cmp) {
      case EQ:
        return Kind.EQUAL;
      case NE:
        return Kind.DISTINCT;
      case GE:
        return Kind.GEQ;
      case GT:
        return Kind.GT;
      case LE:
        return Kind.LEQ;
      case LT:
        return Kind.LT;
      default:
        throw new UnsupportedOperationException(
            "Cannot connvert NumericComparator: " + cmp.toString());
    }
  }

  private Kind convertNumericComparatorBV(NumericComparator cmp, boolean signed) {
    switch (cmp) {
      case EQ:
        return Kind.EQUAL;
      case NE:
        return Kind.DISTINCT;
      case GE:
        if (signed) {
          return Kind.BITVECTOR_SGE;
        } else {
          return Kind.BITVECTOR_UGE;
        }
      case GT:
        if (signed) {
          return Kind.BITVECTOR_SGT;
        } else {
          return Kind.BITVECTOR_UGT;
        }
      case LE:
        if (signed) {
          return Kind.BITVECTOR_SLE;
        } else {
          return Kind.BITVECTOR_ULE;
        }
      case LT:
        if (signed) {
          return Kind.BITVECTOR_SLT;
        } else {
          return Kind.BITVECTOR_ULT;
        }
      default:
        throw new UnsupportedOperationException(
            "Cannot connvert NumericComparator: " + cmp.toString());
    }
  }

  private Kind convertNumericOperator(
      NumericOperator operator, boolean bvTypes, boolean fpTypes, boolean signed) {
    if (bvTypes) {
      return convertBVNumericOperator(operator, signed);
    } else if (fpTypes) {
      return convertFPNumericOperator(operator);
    } else {
      return convertNormalNumericOperator(operator);
    }
  }

  private Kind convertNormalNumericOperator(NumericOperator operator) {
    switch (operator) {
      case PLUS:
        return Kind.PLUS;
      case MINUS:
        return Kind.MINUS;
      case REM:
        return Kind.INTS_MODULUS;
      case MUL:
        return Kind.MULT;
      case DIV:
        return Kind.DIVISION;
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + operator.toString());
    }
  }

  private Kind convertBVNumericOperator(NumericOperator operator, boolean signed) {
    switch (operator) {
      case DIV:
        if (signed) {
          return Kind.BITVECTOR_SDIV;
        } else {
          return Kind.BITVECTOR_UDIV;
        }
      case MUL:
        return Kind.BITVECTOR_MULT;
      case REM:
        if (signed) {
          return Kind.BITVECTOR_SREM;
        } else {
          return Kind.BITVECTOR_UREM;
        }
      case PLUS:
        return Kind.BITVECTOR_PLUS;
      case MINUS:
        return Kind.BITVECTOR_SUB;
      default:
        throw new UnsupportedOperationException("Cannot convert operator: " + operator.toString());
    }
  }

  private Kind convertFPNumericOperator(NumericOperator operator) {
    switch (operator) {
      case DIV:
        return Kind.FLOATINGPOINT_DIV;
      case MUL:
        return Kind.FLOATINGPOINT_MULT;
      case MINUS:
        return Kind.FLOATINGPOINT_SUB;
      case PLUS:
        return Kind.FLOATINGPOINT_PLUS;
      case REM:
        return Kind.FLOATINGPOINT_REM;
      default:
        throw new UnsupportedOperationException("Cannot convert: " + operator.toString());
    }
  }

  private boolean isBVType(Expression left, Expression right) {
    return left.getType() instanceof ConcreteBVIntegerType
        || right.getType() instanceof ConcreteBVIntegerType;
  }

  private boolean isFPType(Expression left, Expression right) {
    return left.getType() instanceof ConcreteFloatingPointType
        || right.getType() instanceof ConcreteFloatingPointType;
  }

  private boolean isSigned(Expression left, Expression right) {
    return left.getType() instanceof ConcreteBVIntegerType
            && ((ConcreteBVIntegerType) left.getType()).isSigned()
        || right.getType() instanceof ConcreteBVIntegerType
            && ((ConcreteBVIntegerType) right.getType()).isSigned();
  }
}
