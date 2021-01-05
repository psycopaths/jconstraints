/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377
 * the original license is:
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues
 * under Apache 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class StringCompoundExpression extends AbstractStringExpression {

  private final Expression<?> main;
  private final Expression<?>[] expressions;
  private final Expression<?> dst;
  private final StringOperator operator;
  private final Expression<?> offset;
  private final Expression<?> length;
  private final Expression<?> position;
  private final Expression<?> src;

  public static StringCompoundExpression createConcat(Expression<?>... expressions) {
    if (expressions.length > 1) {
      return new StringCompoundExpression(
          null, StringOperator.CONCAT, expressions, null, null, null, null, null);
    }
    throw new IllegalArgumentException();
  }

  public static StringCompoundExpression createToString(Expression<?> main) {
    return new StringCompoundExpression(
        main, StringOperator.TOSTR, null, null, null, null, null, null);
  }

  public static StringCompoundExpression createAt(Expression<?> main, Expression<?> position) {
    if (position.getType().equals(BuiltinTypes.SINT32)) {
      position = CastExpression.create(position, BuiltinTypes.INTEGER);
    }
    return new StringCompoundExpression(
        main, StringOperator.AT, null, null, null, null, null, position);
  }

  public static StringCompoundExpression createSubstring(
      Expression<?> main, Expression<?> offset, Expression<?> length) {
    return new StringCompoundExpression(
        main, StringOperator.SUBSTR, null, offset, length, null, null, null);
  }

  public static StringCompoundExpression createReplace(
      Expression<?> main, Expression<?> src, Expression<?> dst) {
    return new StringCompoundExpression(
        main, StringOperator.REPLACE, null, null, null, src, dst, null);
  }

  public static StringCompoundExpression createToLower(Expression<?> main) {
    return new StringCompoundExpression(
        main, StringOperator.TOLOWERCASE, null, null, null, null, null, null);
  }

  public static StringCompoundExpression createToUpper(Expression<?> main) {
    return new StringCompoundExpression(
        main, StringOperator.TOUPPERCASE, null, null, null, null, null, null);
  }

  public StringCompoundExpression(
      Expression<?> main,
      StringOperator operator,
      Expression<?>[] expressions,
      Expression<?> offset,
      Expression<?> length,
      Expression<?> src,
      Expression<?> dst,
      Expression<?> position) {
    this.main = main;
    this.src = src;
    this.dst = dst;
    this.operator = operator;
    this.length = length;
    this.expressions = expressions;
    this.offset = offset;
    this.position = position;
  }

  @Override
  public String evaluate(Valuation values) {
    switch (operator) {
      case AT:
        return evaluateAt(values);
      case CONCAT:
        return evaluateConcat(values);
      case REPLACE:
        return evaluateReplace(values);
      case SUBSTR:
        return evaluateSubstring(values);
      case TOSTR:
        return evaluateToString(values);
      case TOLOWERCASE:
        return evaluateToLower(values);
      case TOUPPERCASE:
        return evaluateToUpper(values);
      default:
        throw new IllegalArgumentException();
    }
  }

  private String evaluateAt(Valuation values) {
    String string = (String) main.evaluate(values);
    BigInteger pos = (BigInteger) position.evaluate(values);
    return String.valueOf(string.charAt(pos.intValue()));
  }

  private String evaluateReplace(Valuation values) {
    String string = (String) main.evaluate(values);
    String source = (String) src.evaluate(values);
    String destination = (String) dst.evaluate(values);
    return string.replace(source, destination);
  }

  private String evaluateSubstring(Valuation values) {
    String string = (String) main.evaluate(values);
    BigInteger of = (BigInteger) offset.evaluate(values);
    BigInteger len = (BigInteger) length.evaluate(values);
    return string.substring(of.intValue(), of.intValue() + len.intValue());
  }

  private String evaluateToString(Valuation values) {
    BigInteger toStr = (BigInteger) main.evaluate(values);
    return String.valueOf(toStr.intValue());
  }

  private String evaluateConcat(Valuation values) {
    String concatString = "";
    for (Expression<?> e : expressions) {
      concatString += (String) e.evaluate(values);
    }
    return concatString;
  }

  private String evaluateToLower(Valuation values) {
    String eval = (String) main.evaluate(values);
    return eval.toLowerCase();
  }

  private String evaluateToUpper(Valuation values) {
    String eval = (String) main.evaluate(values);
    return eval.toUpperCase();
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    if (this.main != null) {
      main.collectFreeVariables(variables);
    }
    if (this.expressions != null) {
      for (Expression<?> e : expressions) {
        e.collectFreeVariables(variables);
      }
    }
    if (this.offset != null) {
      this.offset.collectFreeVariables(variables);
    }
    if (this.length != null) {
      this.length.collectFreeVariables(variables);
    }
    if (this.src != null) {
      this.src.collectFreeVariables(variables);
    }
    if (this.dst != null) {
      this.dst.collectFreeVariables(variables);
    }
    if (this.position != null) {
      this.position.collectFreeVariables(variables);
    }
  }

  public Expression<?> getMain() {
    return main;
  }

  public Expression<?>[] getExpressions() {
    return expressions;
  }

  public Expression<?> getDst() {
    return dst;
  }

  public StringOperator getOperator() {
    return operator;
  }

  public Expression<?> getOffset() {
    return offset;
  }

  public Expression<?> getLength() {
    return length;
  }

  public Expression<?> getPosition() {
    return position;
  }

  public Expression<?> getSrc() {
    return src;
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Expression<?>[] getChildren() {
    ArrayList<Expression<?>> children = new ArrayList<>();
    // It is very important to keep the order in which those expressions are added to the list.
    // The oder ensures that they keep up in the right order at the smt command.
    checkAndAdd(main, children);
    if (expressions != null) {
      children.addAll(Arrays.asList(expressions));
    }
    checkAndAdd(offset, children);
    checkAndAdd(length, children);
    checkAndAdd(src, children);
    checkAndAdd(dst, children);
    checkAndAdd(position, children);
    return children.toArray(new Expression[0]);
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    switch (operator) {
      case AT:
        a.append("(" + operator + " ");
        main.print(a, flags);
        a.append(" " + position + ") ");
        break;
      case CONCAT:
        printConcat(a, flags);
        break;
      case REPLACE:
        a.append("(" + operator + " ");
        main.print(a, flags);
        src.print(a, flags);
        dst.print(a, flags);
        a.append(") ");
        break;
      case SUBSTR:
        a.append("(" + operator + " ");
        main.print(a, flags);
        offset.print(a, flags);
        length.print(a, flags);
        a.append(") ");
        break;
      case TOSTR:
        appendDefault(a, flags);
        break;
      case TOLOWERCASE:
        appendDefault(a, flags);
        break;
      case TOUPPERCASE:
        appendDefault(a, flags);
        break;
      default:
        throw new IllegalArgumentException();
    }
  }

  private void appendDefault(Appendable a, int flags) throws IOException {
    a.append("(" + operator + " ");
    main.print(a, flags);
    a.append(") ");
  }

  private void printConcat(Appendable a, int flags) throws IOException {

    a.append('(');
    a.append(operator.toString());
    for (Expression<?> e : expressions) {
      a.append(" ");
      e.print(a, flags);
    }
    a.append(") ");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    print(a, flags);
  }

  private void checkAndAdd(Expression expr, List<Expression<?>> list) {
    if (expr != null) {
      list.add(expr);
    }
  }
}
