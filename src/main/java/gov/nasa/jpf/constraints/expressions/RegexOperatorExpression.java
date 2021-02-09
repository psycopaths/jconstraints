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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.io.IOException;
import java.util.Collection;
import java.util.regex.Pattern;

public class RegexOperatorExpression extends AbstractRegExExpression {

  private final Expression<?> left;
  private final RegExOperator operator;
  private final int low;
  private final int high;
  private final char ch1;
  private final char ch2;
  private final String s;

  private RegexOperatorExpression(
      Expression<?> left, RegExOperator operator, int low, int high, char ch1, char ch2, String s) {
    this.left = left;
    this.operator = operator;
    this.low = low;
    this.high = high;
    this.ch1 = ch1;
    this.ch2 = ch2;
    this.s = s;
  }

  public static RegexOperatorExpression createLoop(Expression<?> left, int low) {
    return new RegexOperatorExpression(left, RegExOperator.LOOP, low, low, '0', '0', "");
  }

  public static RegexOperatorExpression createLoop(Expression<?> left, int low, int high) {
    return new RegexOperatorExpression(left, RegExOperator.LOOP, low, high, '0', '0', "");
  }

  public static RegexOperatorExpression createKleeneStar(Expression<?> left) {
    return new RegexOperatorExpression(left, RegExOperator.KLEENESTAR, 0, 0, '0', '0', "");
  }

  public static RegexOperatorExpression createKleenePlus(Expression<?> left) {
    return new RegexOperatorExpression(left, RegExOperator.KLEENEPLUS, 0, 0, '0', '0', "");
  }

  public static RegexOperatorExpression createOptional(Expression<?> left) {
    return new RegexOperatorExpression(left, RegExOperator.OPTIONAL, 0, 0, '0', '0', "");
  }

  public static RegexOperatorExpression createRange(char ch1, char ch2) {
    return new RegexOperatorExpression(null, RegExOperator.RANGE, 0, 0, ch1, ch2, "");
  }

  public static RegexOperatorExpression createStrToRe(String s) {
    return new RegexOperatorExpression(null, RegExOperator.STRTORE, 0, 0, '0', '0', s);
  }

  public static RegexOperatorExpression createStrToRe(Expression expr) {
    return new RegexOperatorExpression(expr, RegExOperator.STRTORE, 0, 0, '0', '0', null);
  }

  public static RegexOperatorExpression createComplement(Expression left) {
    return new RegexOperatorExpression(left, RegExOperator.COMPLEMENT, 0, 0, '0', '0', null);
  }

  public static RegexOperatorExpression createAllChar() {
    return new RegexOperatorExpression(null, RegExOperator.ALLCHAR, 0, 0, '0', '0', "");
  }

  public static RegexOperatorExpression createAll() {
    return new RegexOperatorExpression(null, RegExOperator.ALL, 0, 0, '0', '0', "");
  }

  public static RegexOperatorExpression createNoChar() {
    return new RegexOperatorExpression(null, RegExOperator.NOSTR, 0, 0, '0', '0', "");
  }

  public Expression<?> getLeft() {
    return left;
  }

  public int getLow() {
    return low;
  }

  public int getHigh() {
    return high;
  }

  public char getCh1() {
    return ch1;
  }

  public char getCh2() {
    return ch2;
  }

  public String getS() {
    return s;
  }

  public RegExOperator getOperator() {
    return operator;
  }

  @Override
  public String evaluate(Valuation values) {
    String regex = left != null ? (String) left.evaluate(values) : "";
    return evaluateOperator(regex);
  }

  @Override
  public String evaluateSMT(Valuation values) {
    String regex = left != null ? (String) left.evaluateSMT(values) : "";
    return evaluateOperator(regex);
  }

  private String evaluateOperator(String regex) {
    switch (operator) {
      case ALL:
        return "(.*)";
      case ALLCHAR:
        return "(.)";
      case KLEENEPLUS:
        return "(" + regex + ")+";
      case KLEENESTAR:
        return "(" + regex + ")*";
      case LOOP:
        return "(" + regex + "){" + low + "," + high + "}";
      case NOSTR:
        return "(^.*)";
      case OPTIONAL:
        return "(" + regex + ")?";
      case RANGE:
        return "[" + ch1 + "-" + ch2 + "]";
      case STRTORE:
        String content = s != null ? s : regex;
        return Pattern.quote(content);
      case COMPLEMENT:
        throw new UnsupportedOperationException("semantic?");
      default:
        throw new IllegalArgumentException();
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    if (this.left != null) {
      this.left.collectFreeVariables(variables);
    }
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[] {left};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    switch (operator) {
      case ALLCHAR:
        a.append(operator + " ");
        break;
      case KLEENEPLUS:
        a.append("(");
        left.print(a, flags);
        a.append(") ");
        break;
      case KLEENESTAR:
        a.append("(");
        left.print(a, flags);
        a.append(") ");
        break;
      case LOOP:
        a.append("((_ " + operator + " " + low + " " + high + ") ");
        left.print(a, flags);
        a.append(") ");
        break;
      case NOSTR:
        a.append(operator + " ");
        break;
      case OPTIONAL:
        a.append("(" + operator);
        left.print(a, flags);
        a.append(") ");
        break;
      case RANGE:
        a.append("( " + operator + " " + ch1 + " " + ch2 + ") ");
        break;
      case STRTORE:
        a.append("(" + operator + " " + s + ") ");
        break;
      default:
        throw new IllegalArgumentException();
    }
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    // TODO Auto-generated method stub

  }
}
