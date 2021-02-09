/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.ExpressionOperator;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanOperator;
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
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.io.StringReader;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_exit;
import org.smtlib.command.C_get_model;
import org.smtlib.command.C_set_info;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.HexLiteral;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.impl.Sort;

public class SMTLIBParser {

  private final Set<Variable> letContext;
  public SMTProblem problem;

  public SMTLIBParser() {
    problem = new SMTProblem();
    letContext = new HashSet<>();
  }

  public static SMTProblem parseSMTProgram(final String input)
      throws IOException, IParser.ParserException, SMTLIBParserException {
    final SMT smt = new SMT();

    final ISource toBeParsed =
        smt.smtConfig.smtFactory.createSource(
            new CharSequenceReader(new StringReader(input), input.length(), 100, 2), null);
    final IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, toBeParsed);
    final SMTLIBParser smtParser = new SMTLIBParser();

    while (!parser.isEOD()) {
      ICommand cmd = parser.parseCommand();
      if (cmd instanceof C_declare_fun) {
        smtParser.processDeclareFun((C_declare_fun) cmd);
      } else if (cmd instanceof C_assert) {
        smtParser.processAssert((C_assert) cmd);
      } else if (cmd instanceof C_check_sat) {
        // It is okay, if check_sat is the last command in the chain, but it is just ignored.
        if (!parser.isEOD()) {
          cmd = parser.parseCommand();
          if (!(cmd instanceof C_exit || cmd instanceof C_get_model)) {
            throw new SMTLIBParserNotSupportedException(
                "Check sat is only at the end of a smt problem allowed or a get_model is"
                    + " required.");
          }
        }
      } else if (cmd instanceof C_set_info
          || cmd instanceof C_set_logic
          || cmd instanceof C_set_option) {
        // It is safe to ignore the info commands.
      } else {
        throw new SMTLIBParserNotSupportedException("Cannot pare the following command: " + cmd);
      }
    }
    return smtParser.problem;
  }

  public Expression processAssert(final C_assert cmd) throws SMTLIBParserException {
    final Expression res = processExpression(cmd.expr());
    problem.addAssertion(res);
    return res;
  }

  public void processDeclareFun(final C_declare_fun cmd) throws SMTLIBParserException {
    if (cmd.argSorts().size() != 0) {
      throw new SMTLIBParserNotSupportedException(
          "Cannot convert the declared function, because argument size is not null. Might be"
              + " implemented in the future.");
    }
    if (!(cmd.resultSort() instanceof Sort.Application)) {
      throw new SMTLIBParserException("Could only convert type of type NamedSort.Application");
    }
    final Sort.Application application = (Sort.Application) cmd.resultSort();

    final Type<?> type = TypeMap.getType(application.toString());
    if (type == null) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Could not resolve type declared in function: " + application.toString());
    }
    final Variable var = Variable.create(type, cmd.symbol().toString());
    problem.addVariable(var);
  }

  private <E> Expression<E> processArgument(final IExpr arg) throws SMTLIBParserException {
    Expression<E> resolved = null;
    if (arg instanceof ISymbol) {
      resolved = resolveSymbol((ISymbol) arg);
    } else if (arg instanceof INumeral) {
      resolved = resolveNumeral((INumeral) arg);
    } else if (arg instanceof IDecimal) {
      resolved = resolveDecimal((IDecimal) arg);
    } else if (arg instanceof FcnExpr) {
      resolved = processFunctionExpression((FcnExpr) arg);
    } else if (arg instanceof Let) {
      resolved = processLetExpression((Let) arg);
    } else if (arg instanceof IStringLiteral) {
      resolved = resolveStringLiteral((IStringLiteral) arg);
    } else if (arg instanceof HexLiteral) {
      resolved = resolveHexLiteral((HexLiteral) arg);
    } else {
      throw new SMTLIBParserNotSupportedException(
          "The arguments type is not supported: " + arg.getClass());
    }
    return successfulArgumentProcessing(resolved, arg);
  }

  private Constant resolveHexLiteral(HexLiteral arg) {
    String value = arg.toString().replace("#x", "");
    if (value.length() == 2) {
      return Constant.create(BuiltinTypes.SINT8, Byte.parseByte(value, 16));
    } else if (value.length() == 8) {
      return Constant.create(BuiltinTypes.SINT32, Integer.parseUnsignedInt(value, 16));
    } else if (value.length() == 16) {
      return Constant.create(BuiltinTypes.SINT64, Long.parseUnsignedLong(value, 16));
    } else {
      throw new IllegalArgumentException("Wrong byte size in the hex value: #x" + value);
    }
  }

  private Expression processExpression(final IExpr expr) throws SMTLIBParserException {
    Expression res = null;
    if (expr instanceof FcnExpr) {
      res = processFunctionExpression((FcnExpr) expr);
    } else if (expr instanceof Let) {
      res = processLetExpression((Let) expr);
    } else if (expr instanceof Symbol) {
      res = resolveSymbol((ISymbol) expr);
    } else {
      throw new SMTLIBParserNotSupportedException(
          "Cannot pare the subexpression of type: " + expr.getClass());
    }
    return res;
  }

  private Expression processLetExpression(final Let sExpr) throws SMTLIBParserException {
    final List<Variable> parameters = new ArrayList();
    final Map<Variable, Expression> parameterValues = new HashMap<>();
    for (final IExpr.IBinding binding : sExpr.bindings()) {
      final Expression parameterValue = processExpression(binding.expr());
      final Variable parameter =
          Variable.create(parameterValue.getType(), binding.parameter().value());
      parameters.add(parameter);
      parameterValues.put(parameter, parameterValue);
    }
    letContext.addAll(parameters);
    final Expression mainValue = processExpression(sExpr.expr());
    letContext.removeAll(parameters);
    return LetExpression.create(parameters, parameterValues, mainValue);
  }

  private Expression processFunctionExpression(final FcnExpr sExpr) throws SMTLIBParserException {
    final String operatorStr = sExpr.head().headSymbol().value();
    final Queue<Expression> convertedArguments = new LinkedList<>();
    for (final IExpr arg : sExpr.args()) {
      final Expression jExpr = processArgument(arg);
      convertedArguments.add(jExpr);
    }
    if (operatorStr.equals("re.loop")) {
      String tmp = sExpr.toString();
      Pattern p = Pattern.compile("[+-]?[0-9]+");
      Matcher m = p.matcher(tmp);
      SMT smt = new SMT();
      IExpr.IFactory efactory = smt.smtConfig.exprFactory;
      m.find();
      IExpr low = efactory.numeral(m.group());
      m.find();
      IExpr high = efactory.numeral(m.group());
      convertedArguments.add(processArgument(low));
      convertedArguments.add(processArgument(high));
    }
    Expression ret = null;
    if (operatorStr.equals("not")) {
      ret = createNegation(convertedArguments);
    } else if (operatorStr.equals("ite")) {
      ret = createITE(convertedArguments);
    } else if (operatorStr.equals("int2bv")) {
      ParameterizedIdentifier pi = (ParameterizedIdentifier) sExpr.head();
      ret = createCastToBV(convertedArguments, pi.numerals().get(0).intValue());
    } else if (operatorStr.equals("bv2nat")) {
      ret = CastExpression.create(convertedArguments.poll(), BuiltinTypes.INTEGER);
    } else if (operatorStr.equals("distinct")) {
      ExpressionOperator eo = EQ;
      ret = createExpression(fixExpressionOperator(eo, convertedArguments), convertedArguments);
      ret = Negation.create(ret);
    } else {
      final ExpressionOperator operator =
          ExpressionOperator.fromString(
              FunctionOperatorMap.getjConstraintOperatorName(operatorStr));
      ret = createExpression(operator, convertedArguments);
    }
    return ret;
  }

  private Expression createCastToBV(Queue<Expression> convertedArguments, int bitSize) {
    if (bitSize == 8) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT8);
    } else if (bitSize == 16) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT16);
    } else if (bitSize == 32) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT32);
    } else if (bitSize == 64) {
      return CastExpression.create(convertedArguments.poll(), BuiltinTypes.SINT64);
    } else {
      throw new IllegalArgumentException("Cannot cast to bitSize: " + bitSize);
    }
  }

  private Negation createNegation(final Queue<Expression> arguments) throws SMTLIBParserException {
    if (arguments.size() == 1) {
      return Negation.create(arguments.poll());
    } else {
      throw new SMTLIBParserException("Cannot use more than one Argument in a Negation Expr");
    }
  }

  private IfThenElse createITE(final Queue<Expression> arguments) throws SMTLIBParserException {
    if (arguments.size() == 3) {
      return IfThenElse.create(arguments.poll(), arguments.poll(), arguments.poll());
    } else {
      throw new SMTLIBParserException(
          "Cannot convert ite-Expr with anything else than three arguments");
    }
  }

  private Expression createExpression(
      final ExpressionOperator operator, final Queue<Expression> arguments)
      throws SMTLIBParserNotSupportedException, SMTLIBParserExceptionInvalidMethodCall {

    checkOperatorNotNull(operator);
    checkImpliesOperatorRequirements(operator, arguments);

    final ExpressionOperator newOperator = fixExpressionOperator(operator, arguments);
    if (!(newOperator instanceof StringBooleanOperator
        || newOperator instanceof StringIntegerOperator
        || newOperator instanceof StringOperator
        || newOperator instanceof RegExCompoundOperator
        || newOperator instanceof RegExOperator
        || newOperator instanceof RegExBooleanOperator)) {
      Expression expr = arguments.poll();
      if (arguments.peek() == null) {
        if (newOperator == NumericOperator.MINUS && expr != null) {
          expr = UnaryMinus.create(expr);
        } else {
          arguments.add(expr);
          throw new SMTLIBParserExceptionInvalidMethodCall(
              "It is strict required, that an operator "
                  + "is "
                  + "passed together with at least two "
                  + "arguments in the "
                  + "queue"
                  + ".\n"
                  + "This call got passed "
                  + "operator: "
                  + operator
                  + " arguments: "
                  + arguments);
        }
      }
      while (arguments.peek() != null) {
        final Expression next = arguments.poll();

        Tuple<Expression, Expression> t = equalizeTypes(expr, next);
        if (newOperator instanceof NumericOperator) {
          expr = NumericCompound.create(t.left, (NumericOperator) newOperator, t.right);
        } else if (newOperator instanceof LogicalOperator) {
          expr = PropositionalCompound.create(t.left, (LogicalOperator) newOperator, t.right);
        } else if (newOperator instanceof BitvectorOperator) {
          expr = BitvectorExpression.create(t.left, (BitvectorOperator) newOperator, t.right);
        } else if (newOperator instanceof NumericComparator) {
          expr = NumericBooleanExpression.create(t.left, (NumericComparator) newOperator, t.right);
        }
      }
      return expr;
    } else if (newOperator instanceof StringOperator) {
      switch ((StringOperator) newOperator) {
        case AT:
          return StringCompoundExpression.createAt(arguments.poll(), arguments.poll());
        case CONCAT:
          Expression<?> tmpexpr[] = new Expression<?>[arguments.size()];
          tmpexpr[0] = arguments.poll();
          tmpexpr[1] = arguments.poll();
          for (int i = 2; i < tmpexpr.length; i++) {
            tmpexpr[i] = arguments.poll();
          }
          return StringCompoundExpression.createConcat(tmpexpr);
        case REPLACE:
          return StringCompoundExpression.createReplace(
              arguments.poll(), arguments.poll(), arguments.poll());
        case SUBSTR:
          return StringCompoundExpression.createSubstring(
              arguments.poll(), arguments.poll(), arguments.poll());
        case TOSTR:
          return StringCompoundExpression.createToString(arguments.poll());
        case TOLOWERCASE:
          return StringCompoundExpression.createToLower(arguments.poll());
        case TOUPPERCASE:
          return StringCompoundExpression.createToUpper(arguments.poll());
        default:
          throw new IllegalArgumentException("Unknown StringCompoundOperator");
      }
    } else if (newOperator instanceof StringBooleanOperator) {
      switch ((StringBooleanOperator) newOperator) {
        case CONTAINS:
          return StringBooleanExpression.createContains(arguments.poll(), arguments.poll());
        case EQUALS:
          return processEquals(arguments.poll(), arguments.poll());
        case PREFIXOF:
          Expression prefix = arguments.poll();
          return StringBooleanExpression.createPrefixOf(arguments.poll(), prefix);
        case SUFFIXOF:
          Expression suffix = arguments.poll();
          return StringBooleanExpression.createSuffixOf(arguments.poll(), suffix);
        default:
          throw new IllegalArgumentException("Unknown StringBooleanOperator: " + newOperator);
      }
    } else if (newOperator instanceof StringIntegerOperator) {
      switch ((StringIntegerOperator) newOperator) {
        case INDEXOF:
          if (arguments.size() == 0) {
            return StringIntegerExpression.createIndexOf(arguments.poll(), arguments.poll());
          } else {
            return StringIntegerExpression.createIndexOf(
                arguments.poll(), arguments.poll(), arguments.poll());
          }
        case LENGTH:
          return StringIntegerExpression.createLength(arguments.poll());
        case TOINT:
          return StringIntegerExpression.createToInt(arguments.poll());
        default:
          throw new IllegalArgumentException("Unknown StringIntegerOperator: " + newOperator);
      }
    } else if (newOperator instanceof RegExOperator) {
      switch ((RegExOperator) newOperator) {
        case ALLCHAR:
          return RegexOperatorExpression.createAllChar();
        case KLEENEPLUS:
          return RegexOperatorExpression.createKleenePlus(arguments.poll());
        case KLEENESTAR:
          return RegexOperatorExpression.createKleeneStar(arguments.poll());
        case LOOP:
          Expression re = arguments.poll();
          Constant lo = (Constant) arguments.poll();
          BigInteger lowLoop = (BigInteger) lo.getValue();

          if (arguments.peek() != null) {
            Constant hi = (Constant) arguments.poll();
            BigInteger highLoop = (BigInteger) hi.getValue();
            return RegexOperatorExpression.createLoop(re, lowLoop.intValue(), highLoop.intValue());
          }
          return RegexOperatorExpression.createLoop(re, (int) lo.getValue());
        case NOSTR:
          return RegexOperatorExpression.createNoChar();
        case OPTIONAL:
          return RegexOperatorExpression.createOptional(arguments.poll());
        case RANGE:
          Constant loR = (Constant) arguments.poll();
          Constant hiR = (Constant) arguments.poll();
          String l = (String) loR.getValue();
          String h = (String) hiR.getValue();
          char low = l.charAt(0);
          char high = h.charAt(0);
          return RegexOperatorExpression.createRange(low, high);
        case STRTORE:
          Expression e = arguments.poll();
          if (e instanceof Constant) {
            Constant expr = (Constant) e;
            return RegexOperatorExpression.createStrToRe((String) expr.getValue());
          }
          return RegexOperatorExpression.createStrToRe(e);
        default:
          throw new UnsupportedOperationException("Unknown RegexOperator: " + newOperator);
      }
    } else if (newOperator instanceof RegExCompoundOperator) {
      return convertRegExCompundOperator(newOperator, arguments);
    } else if (newOperator instanceof RegExBooleanOperator) {
      switch ((RegExBooleanOperator) newOperator) {
        case STRINRE:
          return RegExBooleanExpression.create(arguments.poll(), arguments.poll());
        default:
          throw new UnsupportedOperationException("Unknown RegexBooleanOperator: " + newOperator);
      }
    } else {
      throw new SMTLIBParserNotSupportedException(
          "Cannot convert the following operator class: " + operator.getClass());
    }
  }

  private Expression processEquals(Expression left, Expression right) {
    if (left.getType().equals(BuiltinTypes.STRING)) {
      return StringBooleanExpression.createEquals(left, right);
    } else if (left.getType().equals(BuiltinTypes.BOOL)) {
      return PropositionalCompound.create(left, LogicalOperator.EQUIV, right);
    } else if (left.getType() instanceof NumericType) {
      return NumericBooleanExpression.create(left, EQ, right);
    } else {
      throw new IllegalArgumentException(
          "Unknown StringBooleanOperator arguments: " + left + " " + right);
    }
  }

  private Expression convertRegExCompundOperator(
      ExpressionOperator newOperator, Queue<Expression> arguments) {
    switch ((RegExCompoundOperator) newOperator) {
      case CONCAT:
        Expression<?> tmpexpr[] = new Expression<?>[arguments.size()];
        tmpexpr[0] = arguments.poll();
        tmpexpr[1] = arguments.poll();
        for (int i = 2; i < tmpexpr.length; i++) {
          tmpexpr[i] = arguments.poll();
        }
        return RegexCompoundExpression.createConcat(tmpexpr);
      case INTERSECTION:
        return RegexCompoundExpression.createIntersection(arguments.poll(), arguments.poll());
      case UNION:
        RegexCompoundExpression rce =
            RegexCompoundExpression.createUnion(arguments.poll(), arguments.poll());
        while (!arguments.isEmpty()) {
          rce = RegexCompoundExpression.createUnion(rce, arguments.poll());
        }
        return rce;
      default:
        throw new UnsupportedOperationException("Unknown RegexCompoundOperator: " + newOperator);
    }
  }

  private Constant resolveDecimal(final IDecimal decimal) {
    return Constant.create(BuiltinTypes.DECIMAL, decimal.value());
  }

  private <L, R> Tuple<L, R> equalizeTypes(final Expression left, final Expression right)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (left.getType() == right.getType()) {
      return new Tuple(left, right);
    } else if (left instanceof UnaryMinus && right instanceof UnaryMinus) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Cannot equialize Types for two unary minus expressions");
    } else if ((left instanceof Constant
            || (left instanceof UnaryMinus && ((UnaryMinus) left).getNegated() instanceof Constant))
        && BuiltinTypes.isBuiltinType(right.getType())) {
      final Expression constant = convertTypeConstOrMinusConst(right.getType(), left);
      return new Tuple(constant, right);
    } else if ((right instanceof Constant
            || right instanceof UnaryMinus && ((UnaryMinus) right).getNegated() instanceof Constant)
        && BuiltinTypes.isBuiltinType(left.getType())) {
      final Expression constant = convertTypeConstOrMinusConst(left.getType(), right);
      return new Tuple(left, constant);
    } else {
      Expression righCast = right.as(left.getType());
      if (righCast != null) {
        return new Tuple(left, right);
      }
      Expression leftCast = left.as(right.getType());
      if (leftCast != null) {
        return new Tuple(leftCast, right);
      }
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "The expressions are not equal, but they are also not a constant and another BuiltIn "
              + "expression type which might easily be type casted. left: "
              + left.getType()
              + " and right: "
              + right.getType());
    }
  }

  private Expression convertTypeConstOrMinusConst(final Type type, final Expression expr)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (expr instanceof UnaryMinus) {
      return convertUnaryMinus(type, (UnaryMinus) expr);
    } else if (expr instanceof Constant) {
      return Constant.createCasted(type, (Constant) expr);
    } else {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Expected a Constant or Unary Expression, but got" + expr.getClass());
    }
  }

  private UnaryMinus convertUnaryMinus(final Type type, final UnaryMinus unary) {
    return UnaryMinus.create(Constant.createCasted(type, (Constant) unary.getNegated()));
  }

  private Constant resolveNumeral(final INumeral numeral) {
    return Constant.create(BuiltinTypes.INTEGER, numeral.value());
  }

  private Constant resolveStringLiteral(final IStringLiteral stringliteral) {
    String value = stringliteral.value();
    return Constant.create(BuiltinTypes.STRING, value);
  }

  private Expression resolveSymbol(final ISymbol symbol)
      throws SMTLIBParserExceptionInvalidMethodCall, SMTLIBParserNotSupportedException {
    if (symbol.value().equals("re.nostr")) {
      return createExpression(RegExOperator.NOSTR, new LinkedList<Expression>());
    }
    if (symbol.value().equals("re.allchar")) {
      return createExpression(RegExOperator.ALLCHAR, new LinkedList<Expression>());
    }
    if (symbol.value().equalsIgnoreCase("true")) {
      return ExpressionUtil.TRUE;
    }
    if (symbol.value().equalsIgnoreCase("false")) {
      return ExpressionUtil.FALSE;
    }
    for (final Variable var : problem.variables) {
      if (var.getName().equals(symbol.value())) {
        return var;
      }
    }

    for (final Variable parameter : letContext) {
      if (parameter.getName().equals(symbol.value())) {
        return parameter;
      }
    }
    if (symbol.value().matches("-(\\d)+")) {
      return Constant.create(BuiltinTypes.INTEGER, new BigInteger(symbol.value()));
    }

    throw new SMTLIBParserExceptionInvalidMethodCall("Cannot parse Symbol: " + symbol);
  }

  private <E> Expression<E> successfulArgumentProcessing(final Expression<E> expr, final IExpr arg)
      throws SMTLIBParserException {
    if (expr == null) {
      throw new SMTLIBParserException("Cannot process the following argument: " + arg);
    }
    return expr;
  }

  private boolean checkOperatorNotNull(final ExpressionOperator operator)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (operator == null) {
      throw new SMTLIBParserExceptionInvalidMethodCall(
          "Operator is null. Cannot create Operator dependent Expression!");
    }
    return true;
  }

  private final ExpressionOperator fixExpressionOperator(
      final ExpressionOperator operator, final Queue<Expression> arguments) {
    final Queue<Expression> tmp = new LinkedList<Expression>(arguments);
    final StringBooleanOperator newOperator = StringBooleanOperator.EQUALS;

    if (operator.equals(EQ)) {
      Expression left = tmp.poll();
      Expression right = tmp.poll();
      if (left instanceof StringBooleanExpression
          || left instanceof StringIntegerExpression
          || left instanceof StringCompoundExpression
          || right instanceof StringBooleanExpression
          || right instanceof StringIntegerExpression
          || right instanceof StringCompoundExpression) {
        return newOperator;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.StringType) {
          return newOperator;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.StringType) {
          return newOperator;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof StringBooleanExpression) {
        return newOperator;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof StringBooleanExpression) {
        return newOperator;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.EQUIV;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.EQUIV;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.EQUIV;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.EQUIV;
      }
    }

    if (operator.equals(NumericComparator.NE)) {
      Expression left = tmp.poll();
      Expression right = tmp.poll();
      if (left instanceof PropositionalCompound || right instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }
      if (left instanceof Variable<?> || left instanceof Constant<?>) {
        if (left.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.XOR;
        }
      }
      if (right instanceof Variable<?> || right instanceof Constant<?>) {
        if (right.getType() instanceof BuiltinTypes.BoolType) {
          return LogicalOperator.XOR;
        }
      }
      if (right instanceof Negation
          && ((Negation) right).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }

      if (left instanceof Negation
          && ((Negation) left).getNegated() instanceof PropositionalCompound) {
        return LogicalOperator.XOR;
      }
    }
    return operator;
  }

  private boolean checkImpliesOperatorRequirements(
      final ExpressionOperator operator, final Queue<Expression> arguments)
      throws SMTLIBParserExceptionInvalidMethodCall {
    if (operator.equals(LogicalOperator.IMPLY)) {
      if (arguments.size() == 2) {
        return true;
      } else {
        throw new SMTLIBParserExceptionInvalidMethodCall(
            "Implies can only work with exactly two arguments, but got: " + arguments);
      }
    }
    return false;
  }

  private static class Tuple<L, R> {
    protected L left;
    protected R right;

    private Tuple(final L left, final R right) {
      this.left = left;
      this.right = right;
    }
  }
}
