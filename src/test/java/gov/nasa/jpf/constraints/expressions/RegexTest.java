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

/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * <p>Copyright (C) 2015, United States Government, as represented by the Administrator of the
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
 * <p>Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com) We
 * license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.expressions;

import static org.testng.AssertJUnit.assertEquals;
import static org.testng.AssertJUnit.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.math.BigInteger;
import java.util.Properties;
import org.testng.annotations.Test;

public class RegexTest {
  public static void main(String[] args) {
    RegexTest t = new RegexTest();
    //		String regex1="(?=[a-z][aeiou]t)[a-z][aeiou]t";
    //		String regex= "((?=[a-z][aeiou]t)c[a-z][a-z])";
    //	    Pattern expression = Pattern.compile(regex);
    ////	    System.out.println("Pattern: " + expression);
    //
    //	    String string1 = "catbadsadcarcit";
    //	    Matcher m= expression.matcher(string1);
    //	    while(m.find()) {
    //	    	System.out.println(m.group());
    //	    }
    // String regex = "[0-8]";
    //		String string = "WWWWW's Birthday is 124-17-77";
    //
    //		String regex = "W(.*)[0-9]([0-3]|[5-9])-([0-9]{2,2})-([0-9]{2,2})";
    //		System.out.println(string.matches(regex));
    //		Pattern expression = Pattern.compile("W.*\\d[0-35-9]-\\d\\d-\\d\\d");
    //		String string1 = args[0];
    //		Matcher matcher = expression.matcher(string1);
    //		while (matcher.find()) {
    //			System.out.println(matcher.group());
    //			String tmp = matcher.group();
    //			assert tmp.equals("WWWWW's Birthday is 12-17-77");

    t.testSequenceSolver();
  }

  @Test
  public void testConcat() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=z3str3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();

    Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
    Constant<String> c1 = Constant.create(BuiltinTypes.STRING, "Welt");
    StringBooleanExpression e1 = StringBooleanExpression.createContains(v1, c1);
    Expression halloWelt =
        RegexCompoundExpression.createConcat(
            RegexOperatorExpression.createStrToRe("Hallo"),
            RegexOperatorExpression.createStrToRe("Welt"));
    Expression<Boolean> res = RegExBooleanExpression.create(v1, halloWelt);

    ConstraintSolver solver = factory.createSolver("z3", conf);
    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(ExpressionUtil.and(e1, res), val);
    assertEquals(result, ConstraintSolver.Result.SAT);
    assertEquals(val.getValue("v1"), "HalloWelt");
    assertTrue(res.evaluate(val));
  }

  @Test
  public void testIntegerAndStringMixture() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=z3str3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    System.out.println("Simple Tests");
    ConstraintSolver solver = factory.createSolver("z3", conf);
    Variable<String> w = Variable.create(BuiltinTypes.STRING, "w");
    Constant<String> m = Constant.create(BuiltinTypes.STRING, "M");
    Variable i = Variable.create(BuiltinTypes.INTEGER, "i");
    NumericCompound nc1 =
        new NumericCompound(
            i, NumericOperator.MINUS, Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(1)));
    NumericCompound nc2 =
        new NumericCompound(
            Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(5)), NumericOperator.MINUS, i);
    StringCompoundExpression sce1 = StringCompoundExpression.createAt(w, nc1);
    StringBooleanExpression sbe = StringBooleanExpression.createEquals(m, sce1);
    NumericBooleanExpression nbe =
        NumericBooleanExpression.create(
            Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(3)),
            NumericComparator.EQ,
            nc2);
    Expression<Boolean> finalExpr = ExpressionUtil.and(sbe, nbe);
    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(finalExpr, val);
    assertEquals(result, ConstraintSolver.Result.SAT);
    assertEquals(val.getValue("i"), BigInteger.valueOf(2));
    assertTrue("The valuation should fit the expression", finalExpr.evaluate(val));
  }

  public void testOverlap() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();

    System.out.println(" A string cannot overlap with two different characters. Unsat:");
    ConstraintSolver solver = factory.createSolver("z3", conf);
    Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
    Constant<String> c1 = Constant.create(BuiltinTypes.STRING, "b");
    Constant<String> c2 = Constant.create(BuiltinTypes.STRING, "a");
    Expression<String> e1 = StringCompoundExpression.createConcat(v1, c1);
    StringCompoundExpression e2 = StringCompoundExpression.createConcat(c2, v1);
    StringBooleanExpression boolexp = StringBooleanExpression.createEquals(e1, e2);
    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(boolexp, val);
    System.out.println("result: " + result);
    System.out.println("valuation: " + val);
    System.out.println("");
    System.out.println("Strings a, b, c can have a non-trivial overlap. ");
    Variable<String> v2 = Variable.create(BuiltinTypes.STRING, "v2");
    Variable<String> v3 = Variable.create(BuiltinTypes.STRING, "v3");
    Variable<String> v4 = Variable.create(BuiltinTypes.STRING, "v4");
    Constant<String> c3 = Constant.create(BuiltinTypes.STRING, "abcd");
    Constant<String> c4 = Constant.create(BuiltinTypes.STRING, "cdef");
    StringCompoundExpression e3 = StringCompoundExpression.createConcat(v2, v3);
    StringBooleanExpression boolexpr2 = StringBooleanExpression.createEquals(e3, c3);
    StringCompoundExpression e4 = StringCompoundExpression.createConcat(v3, v4);
    StringBooleanExpression boolexpr3 = StringBooleanExpression.createEquals(e4, c4);
    Valuation val2 = new Valuation();
    ConstraintSolver.Result result2 = solver.solve(ExpressionUtil.and(boolexpr2, boolexpr3), val2);
    System.out.println("result: " + result2);
    System.out.println("valuation: " + val2);
    System.out.println("");
  }

  public void testSequenceSolver() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=seq");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    ConstraintSolver solver = factory.createSolver("z3", conf);
    System.out.println("SimpleExample");
    Constant<Integer> c0 = Constant.create(BuiltinTypes.SINT32, 0);
    Variable<Integer> result = Variable.create(BuiltinTypes.SINT32, "result");
    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
    Variable<Integer> i = Variable.create(BuiltinTypes.SINT32, "i");

    NumericBooleanExpression iGE0 = new NumericBooleanExpression(i, NumericComparator.GE, c0);
    NumericBooleanExpression iGEx = new NumericBooleanExpression(i, NumericComparator.GE, x);

    NumericCompound<Integer> iMINUSx = new NumericCompound<Integer>(i, NumericOperator.MINUS, x);
    NumericBooleanExpression resultEQiMINUSx =
        new NumericBooleanExpression(result, NumericComparator.EQ, iMINUSx);

    NumericBooleanExpression resultGE0 =
        new NumericBooleanExpression(result, NumericComparator.GE, c0);

    Expression<Boolean> path1 = ExpressionUtil.and(iGE0, iGEx, resultEQiMINUSx, resultGE0);
    Valuation val = new Valuation();
    ConstraintSolver.Result resultOfPath1 = solver.solve(path1, val);
    assertEquals(resultOfPath1, ConstraintSolver.Result.SAT);

    if (resultOfPath1.equals(ConstraintSolver.Result.SAT)) {
      System.out.println(val);
      System.out.println(path1.evaluate(val));
    }
  }

  public void testRegexMatchs() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=seq");
    System.out.println("property: " + conf.getProperty("symbolic.dp"));
    //	    conf.setProperty("z3.options", "dump_models=false");

    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    ConstraintSolver solver = factory.createSolver("z3", conf);
    System.out.println("RegexMatches02");
    Constant<String> string = Constant.create(BuiltinTypes.STRING, "WWWWW's Birthday is 12-17-77");
    Constant<String> w = Constant.create(BuiltinTypes.REGEX, "W");
    RegexOperatorExpression c09 = RegexOperatorExpression.createRange('0', '9');
    RegexOperatorExpression full = RegexOperatorExpression.createAllChar();
    RegexOperatorExpression c03 = RegexOperatorExpression.createRange('0', '3');
    RegexOperatorExpression c59 = RegexOperatorExpression.createRange('5', '9');
    RegexCompoundExpression union = RegexCompoundExpression.createUnion(c03, c59);
    Constant<String> c2 = Constant.create(BuiltinTypes.REGEX, "-");
    RegexOperatorExpression loop = RegexOperatorExpression.createLoop(c09, 2);
    RegexCompoundExpression completeRegex =
        RegexCompoundExpression.createConcat(w, full, union, c2, loop, c2, loop);

    Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
    RegExBooleanExpression boolexpr = RegExBooleanExpression.create(v1, completeRegex);
    StringBooleanExpression boolexpr2 = StringBooleanExpression.createEquals(string, v1);
    Expression<Boolean> expr = ExpressionUtil.and(boolexpr, boolexpr2);
    Valuation val = new Valuation();
    ConstraintSolver.Result result = solver.solve(expr, val);
    System.out.println("completeRegex: " + completeRegex.evaluate(val));
    System.out.println("expression: " + expr);
    System.out.println("evaluation: " + expr.evaluate(val));
    System.out.println("result: " + result);
    System.out.println("valuation: " + val);
  }
}
