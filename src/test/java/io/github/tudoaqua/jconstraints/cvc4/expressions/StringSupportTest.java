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
package io.github.tudoaqua.jconstraints.cvc4.expressions;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.EQUIV;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.IMPLY;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import edu.stanford.CVC4.CVC4String;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class StringSupportTest {

	CVC4Solver cvc4;
	SolverContext cvc4Context;

	@BeforeMethod
	public void initalize() {
		cvc4 = new CVC4Solver(new HashMap<>());
		cvc4Context = cvc4.createContext();
	}

	@Test
	public void strLenTest() {
		Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable string = Variable.create(BuiltinTypes.STRING, "x1");
		Expression len = StringIntegerExpression.createLength(string);
		len = CastExpression.create(len, BuiltinTypes.SINT32);
		NumericBooleanExpression compLen = NumericBooleanExpression.create(len, NumericComparator.EQ, c5);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(compLen, val);
		assertEquals(res, SAT);
		if (res == SAT) {
			assertTrue(compLen.evaluate(val));
		}
	}

	@Test
	public void strLen2Test() {
		Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable string = Variable.create(BuiltinTypes.STRING, "x1");
		Expression len = StringIntegerExpression.createLength(string);
		len = CastExpression.create(len, BuiltinTypes.SINT32);
		NumericBooleanExpression compLen = NumericBooleanExpression.create(len, NumericComparator.EQ, c5);

		Constant<String> cHallo = Constant.create(BuiltinTypes.STRING, "Hallo");
		StringBooleanExpression strEq = StringBooleanExpression.createEquals(string, cHallo);

		Expression finalExpr = PropositionalCompound.create(compLen, LogicalOperator.AND, strEq);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(finalExpr, val);
		assertEquals(res, SAT);
		boolean equals = compLen.evaluate(val);
		assertTrue(equals);
	}

	@Test
	public void autoCastStrAtTest() {
		Constant c4 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable strVar = Variable.create(BuiltinTypes.STRING, "string0");
		Expression stringAt = StringCompoundExpression.createAt(strVar, c4);
		Constant stringExpected = Constant.create(BuiltinTypes.STRING, "c");
		stringAt = StringBooleanExpression.createEquals(stringAt, stringExpected);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(stringAt, val);
		assertEquals(res, SAT);
		boolean equals = (boolean) stringAt.evaluate(val);
		assertTrue(equals);
	}

	@Test
	public void castStringLen() {
		Constant c_1 = Constant.create(BuiltinTypes.SINT32, 1);

		Variable strVar = Variable.create(BuiltinTypes.STRING, "string0");
		Constant cCase1 = Constant.create(BuiltinTypes.STRING, "case1");

		StringBooleanExpression eqExpr = StringBooleanExpression.createEquals(strVar, cCase1);
		CastExpression castedStringExpression =
				CastExpression.create(StringIntegerExpression.createLength(strVar), BuiltinTypes.SINT32);
		NumericBooleanExpression lenEqExpr =
				NumericBooleanExpression.create(castedStringExpression, NE, UnaryMinus.create(c_1));
		cvc4Context.add(eqExpr);
		cvc4Context.add(lenEqExpr);

		ConstraintSolver.Result res = cvc4Context.isSatisfiable();
		assertEquals(res, SAT);
	}

	@Test
	public void toLowerCaseTest() {
		Variable var = Variable.create(BuiltinTypes.STRING, "x");
		Constant cU = Constant.create(BuiltinTypes.STRING, "UpperCase");
		Constant target = Constant.create(BuiltinTypes.STRING, "uppercase");

		StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
		StringCompoundExpression lower = StringCompoundExpression.createToLower(var);
		StringBooleanExpression part2 = StringBooleanExpression.createEquals(lower, target);
		PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(complete, val);
		assertEquals(res, SAT);
		assertTrue(complete.evaluate(val));
	}

	@Test
	public void toUpperCaseTest() {
		Variable var = Variable.create(BuiltinTypes.STRING, "x");
		Constant cU = Constant.create(BuiltinTypes.STRING, "uppercase");
		Constant target = Constant.create(BuiltinTypes.STRING, "UPPERCASE");

		StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
		StringCompoundExpression upper = StringCompoundExpression.createToUpper(var);
		StringBooleanExpression part2 = StringBooleanExpression.createEquals(upper, target);
		PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(complete, val);
		assertEquals(res, SAT);
		assertTrue(complete.evaluate(val));
	}

	@Test
	public void toAndFromIntEvaluationTest() {
		Variable x = Variable.create(BuiltinTypes.STRING, "x");
		Constant c = Constant.create(BuiltinTypes.STRING, "10");
		Expression toInt = StringIntegerExpression.createToInt(x);
		Expression fromInt = StringCompoundExpression.createToString(toInt);
		StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, c);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(equals, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(equals.evaluate(val));
	}

	@Test
	public void conversionTest() {
		//this test case models: (='_string2'(str.at '_string0' (integer)((sint32)(str.len '_string0')  - 1)) )

		Variable string1 = Variable.create(BuiltinTypes.STRING, "string0");
		Variable string2 = Variable.create(BuiltinTypes.STRING, "string2");


		StringIntegerExpression string1Len = StringIntegerExpression.createLength(string1);

		Expression castedString1Len = CastExpression.create(string1Len, BuiltinTypes.SINT32);
		Expression stringExists =
				NumericBooleanExpression.create(castedString1Len, GT, Constant.create(BuiltinTypes.SINT32, 5));
		Expression arithmetik =
				NumericCompound.create(castedString1Len, NumericOperator.MINUS, Constant.create(BuiltinTypes.SINT32, 1));
		Expression castBack = CastExpression.create(arithmetik, BuiltinTypes.INTEGER);
		Expression charAt = StringCompoundExpression.createAt(string1, castBack);
		Expression equals = StringBooleanExpression.createEquals(string2, charAt);

		Expression complete = PropositionalCompound.create(stringExists, AND, equals);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(complete, val);
		assertEquals(res, SAT);
		assertTrue((Boolean) complete.evaluate(val));
	}

	@Test
	public void strIndexOf1() {
		Variable str = Variable.create(BuiltinTypes.STRING, "str");
		Constant c = Constant.create(BuiltinTypes.STRING, "/");

		Expression complete = StringIntegerExpression.createIndexOf(str, c);
		complete = NumericBooleanExpression
				.create(complete, NE, Constant.create(BuiltinTypes.INTEGER, BigInteger
						.valueOf(-1l)));
		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(complete, val);
		assertEquals(res, SAT);
	}

	@Test
	public void strLastIndexOf1() {
		Variable x = Variable.create(BuiltinTypes.INTEGER, "x");
		Variable y = Variable.create(BuiltinTypes.INTEGER, "y");
		Variable a = Variable.create(BuiltinTypes.STRING, "a");
		Constant b = Constant.create(BuiltinTypes.STRING, "b");
		Constant zero = Constant.create(BuiltinTypes.INTEGER, BigInteger.ZERO);
		Constant ten = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(10));
		Constant hundred = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(100));
		Variable boundedC = Variable.create(BuiltinTypes.INTEGER, "c");
		List<Variable<?>> boundedVars = new LinkedList<>();
		boundedVars.add(boundedC);

		Expression part1 = NumericBooleanExpression
				.create(StringIntegerExpression.createLength(a), GT, ten);
		Expression part2 = NumericBooleanExpression
				.create(StringIntegerExpression.createLength(a), LT, hundred);
		Expression part3 = StringBooleanExpression
				.createEquals(b, StringCompoundExpression.createAt(a, x));
		Expression part4 = PropositionalCompound
				.create(NumericBooleanExpression.create(boundedC, GT, x), AND,
						NumericBooleanExpression.create(boundedC, LE, StringIntegerExpression.createLength(a)));
		Expression part5 = Negation.create(
				StringBooleanExpression.createEquals(b, StringCompoundExpression.createAt(a, boundedC)));
		Expression imply = PropositionalCompound.create(part4, IMPLY, part5);
		Expression forall = new QuantifierExpression(Quantifier.FORALL, boundedVars, imply);
		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(ExpressionUtil.and(part1, part2
				, part3, forall), val);
		assertEquals(res, SAT);
		assertTrue((Boolean) part1.evaluate(val));
		assertTrue((Boolean) part2.evaluate(val));
		assertTrue((Boolean) part3.evaluate(val));
	}

	@Test
	public void stringToReTest() {
		Variable a = Variable.create(BuiltinTypes.STRING, "a");
		Variable regex = Variable.create(BuiltinTypes.STRING, "reg");
		RegexOperatorExpression convRegex = RegexOperatorExpression.createStrToRe(regex);
		RegExBooleanExpression inRegex = RegExBooleanExpression.create(a, convRegex);
		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(inRegex, val);
		assertEquals(res, SAT);
		inRegex.evaluate(val);
	}

	@Test(enabled = false)
	public void stringInReNativeTest() {
		ExprManager em = new ExprManager();
		SmtEngine smt = new SmtEngine(em);
		Expr c1 = em.mkConst(new CVC4String("av"));
		Expr allchar = em.mkConst(Kind.REGEXP_SIGMA);
		String res = smt.checkSat(em.mkExpr(Kind.STRING_IN_REGEXP, c1, allchar)).toString();
		assertTrue(res.equals("unsat"));
	}

	//FIXME: This seems to be a problem in the JAVA API??? (assert (str.in_re "av" re.allchar)) works on commandline.
	@Test(enabled = false)
	public void stringInReTest() {
		Constant c = Constant.create(BuiltinTypes.STRING, "av");
		RegExBooleanExpression rbe = RegExBooleanExpression
				.create(c,
						RegexOperatorExpression.createLoop(RegexOperatorExpression.createAllChar(), 1, 1));
		Expression expr1 = PropositionalCompound.create(rbe, EQUIV, ExpressionUtil.TRUE);
		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(expr1, val);
		assertEquals(res, UNSAT);
	}
}
