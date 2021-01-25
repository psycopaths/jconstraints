/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.smtlibUtility.export;

import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.math.BigInteger;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class StringExpressionTest {
  Variable var;
  Constant constant;
  Constant intConst;

  @BeforeMethod(alwaysRun = true)
  public void initialize() {
    var = Variable.create(BuiltinTypes.STRING, "x");
    constant = Constant.create(BuiltinTypes.STRING, "TEST");
    intConst = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(4));
  }

  @Test(groups = {"base", "smt-export"})
  public void strLengthTest() {
    String expected = "(declare-const x String)\n(assert (str.len x))\n";
    StringIntegerExpression expr = StringIntegerExpression.createLength(var);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strToIntTest() {
    // TODO: This is the Z3 Syntax. QF_S say, this should be str.to_int
    String expected = "(declare-const x String)\n(assert (str.to.int x))\n";
    StringIntegerExpression expr = StringIntegerExpression.createToInt(var);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strIndexOf1Test() {
    String expected = "(declare-const x String)\n(assert (str.indexof x \"TEST\" 4))\n";
    StringIntegerExpression expr = StringIntegerExpression.createIndexOf(var, constant, intConst);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strIndexOf2Test() {
    String expected = "(declare-const x String)\n(assert (str.indexof x \"TEST\" 0))\n";
    StringIntegerExpression expr = StringIntegerExpression.createIndexOf(var, constant);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void concatTest() {
    String expected = "(declare-const x String)\n(assert (str.++ x \"TEST\"))\n";
    StringCompoundExpression expr = StringCompoundExpression.createConcat(var, constant);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void atTest() {
    String expected = "(declare-const x String)\n(assert (str.at x 4))\n";
    StringCompoundExpression expr = StringCompoundExpression.createAt(var, intConst);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void substrTest() {
    String expected = "(declare-const x String)\n(assert (str.substr x 4 4))\n";
    StringCompoundExpression expr =
        StringCompoundExpression.createSubstring(var, intConst, intConst);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void replaceTest() {
    String expected = "(declare-const x String)\n(assert (str.replace x \"TEST\" \"FOO\"))\n";
    StringCompoundExpression expr =
        StringCompoundExpression.createReplace(
            var, constant, Constant.create(BuiltinTypes.STRING, "FOO"));
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void lowerTest() {
    String expected = "(declare-const x String)\n(assert (str.lower x))\n";
    StringCompoundExpression expr = StringCompoundExpression.createToLower(var);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void upperTest() {
    String expected = "(declare-const x String)\n(assert (str.upper x))\n";
    StringCompoundExpression expr = StringCompoundExpression.createToUpper(var);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void toStringTest() {
    // TODO: This is the Z3 Syntax. QF_S say, this should be str.from_int
    String expected = "(assert (int.to.str 4))\n";
    StringCompoundExpression expr = StringCompoundExpression.createToString(intConst);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strEqualsTest() {
    String expected = "(declare-const x String)\n(assert (= x \"TEST\"))\n";
    StringBooleanExpression strBool = StringBooleanExpression.createEquals(var, constant);
    Util.runTest(strBool, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strContainsTest() {
    String expected = "(declare-const x String)\n(assert (str.contains x \"TEST\"))\n";
    StringBooleanExpression strBool = StringBooleanExpression.createContains(var, constant);
    Util.runTest(strBool, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strPrefixOfTest() {
    String expected = "(declare-const x String)\n(assert (str.prefixof x \"TEST\"))\n";
    StringBooleanExpression strBool = StringBooleanExpression.createPrefixOf(var, constant);
    Util.runTest(strBool, expected);
  }

  @Test(groups = {"base", "smt-export"})
  public void strSuffixOfTest() {
    String expected = "(declare-const x String)\n(assert (str.suffixof x \"TEST\"))\n";
    StringBooleanExpression strBool = StringBooleanExpression.createSuffixOf(var, constant);
    Util.runTest(strBool, expected);
  }
}
