/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.TypeContext;
import org.antlr.runtime.RecognitionException;
import org.testng.annotations.Test;

import java.util.HashSet;
import java.util.List;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

/**
 * We just want to assure that a certain set of constraints is parsable without errors
 *
 * @author Malte Mues
 */
public class ExtendedParserTest {
	ParserUtil parser;

	Variable x, b, c;
	HashSet<Variable<?>> vars;

	public ExtendedParserTest() {
		parser = new ParserUtil();
		x = new Variable(BuiltinTypes.SINT8, "x");
		b = new Variable(BuiltinTypes.BOOL, "b");
		c = new Variable(BuiltinTypes.SINT32, "c");
		vars = new HashSet<>();
		vars.add(x);
		vars.add(c);
		vars.add(b);
	}


	@Test(groups = {"parser", "base"})
	public void variableDeclarationOfPrimeVariables() throws RecognitionException, ImpreciseRepresentationException {
		String varDeclaration = "declare x:sint8, b:bool, c:sint32";
		String primeVarDeclaration = "declare x':sint8, b':bool, c':sint32";

		List<Variable<?>> parsedVar = parser.parseVariableDeclaration(varDeclaration);
		parsedVar.addAll(parser.parseVariableDeclaration(primeVarDeclaration));
		assert (parsedVar.contains(x));
		assert (parsedVar.contains(b));
		assert (parsedVar.contains(c));

		Variable xprime, bprime, cprime;
		xprime = new Variable(BuiltinTypes.SINT8, "x'");
		bprime = new Variable(BuiltinTypes.BOOL, "b'");
		cprime = new Variable(BuiltinTypes.SINT32, "c'");
		assert (parsedVar.contains(xprime));
		assert (parsedVar.contains(bprime));
		assert (parsedVar.contains(cprime));
	}

	@Test(groups = {"parser", "base"})
	public void usingPrimeVariables() throws RecognitionException, ImpreciseRepresentationException {
		String testInput = "declare x:sint32, x':sint32 in x > 5 && x' == 5";
		Expression parsedRes = parser.parseLogical(testInput);
		assertEquals(parsedRes.getClass(), PropositionalCompound.class);

		testInput = "declare x':sint32 in forall (x') : (x' > 5b && (exists (c) : (c > x)))";
		parsedRes = parser.parseLogical(testInput, new TypeContext(true), vars);

		assertEquals(QuantifierExpression.class, parsedRes.getClass());
	}

	@Test(groups = {"parser", "base"})
	public void variableDeclaration() throws RecognitionException, ImpreciseRepresentationException {
		String varDeclaration = "declare x:sint8, b:bool, c:sint32";

		List<Variable<?>> parsedVar = parser.parseVariableDeclaration(varDeclaration);

		assert (parsedVar.contains(x));
		assert (parsedVar.contains(b));
		assert (parsedVar.contains(c));
	}

	@Test(groups = {"parser", "base"})
	public void andBooleanExpression() throws RecognitionException, ImpreciseRepresentationException {
		String testString = "declare x:sint8, b:bool, c:sint32 in (c == 5) && (b == false) && (x > c)";
		Expression expr = parser.parseLogical(testString);

		assertTrue(checkAndExpression(expr));

		testString = "declare x:sint8, b:bool, c:sint32 in c == 5 && b == false && x > c";
		expr = parser.parseLogical(testString);

		assertTrue(checkAndExpression(expr));
	}

	@Test(groups = {"parser", "base"})
	public void orBooleanExpression() throws RecognitionException, ImpreciseRepresentationException {
		//the 5b forces the parser to interpret 5 of type sint8. Otherwise an
		//undesired castexpression is added...
		String testString = "x + 5b > c || b == false";
		Expression expr = parser.parseLogical(testString, new TypeContext(true), vars);

		assertEquals(PropositionalCompound.class, expr.getClass());
		PropositionalCompound propCompound = (PropositionalCompound) expr;
		assertEquals(LogicalOperator.OR, propCompound.getOperator());

		NumericBooleanExpression assignmentB = (NumericBooleanExpression) propCompound.getRight();
		assertEquals(b, assignmentB.getLeft());
		assertEquals(NumericComparator.EQ, assignmentB.getComparator());

		assertEquals(NumericBooleanExpression.class, propCompound.getLeft().getClass());
		NumericBooleanExpression comparisonC = (NumericBooleanExpression) propCompound.getLeft();
		assertEquals(NumericComparator.GT, comparisonC.getComparator());
		assertEquals(c, comparisonC.getRight());

		assertEquals(NumericCompound.class, comparisonC.getLeft().getClass());
		NumericCompound additionX = (NumericCompound) comparisonC.getLeft();

		Variable parsedX = (Variable) additionX.getLeft();

		assertEquals(x.getType(), parsedX.getType());
		assertEquals(x.getName(), parsedX.getName());
		assertEquals(x, additionX.getLeft());
		assertEquals(Constant.class, additionX.getRight().getClass());
		assertEquals(NumericOperator.PLUS, additionX.getOperator());
	}

	private boolean checkAndExpression(Expression<Boolean> expr) {
		assertEquals(PropositionalCompound.class, expr.getClass());
		PropositionalCompound propCompound = (PropositionalCompound) expr;
		assertEquals(NumericBooleanExpression.class, propCompound.getRight().getClass());
		assertEquals(LogicalOperator.AND, propCompound.getOperator());
		assertEquals(PropositionalCompound.class, propCompound.getLeft().getClass());

		NumericBooleanExpression comparisonXC = (NumericBooleanExpression) propCompound.getRight();
		propCompound = (PropositionalCompound) propCompound.getLeft();

		assertEquals(x, comparisonXC.getLeft());
		assertEquals(c, comparisonXC.getRight());
		assertEquals(NumericComparator.GT, comparisonXC.getComparator());

		NumericBooleanExpression assignmentC = (NumericBooleanExpression) propCompound.getLeft();
		assertEquals(c, assignmentC.getLeft());
		assertEquals(NumericComparator.EQ, assignmentC.getComparator());

		NumericBooleanExpression assignmentB = (NumericBooleanExpression) propCompound.getRight();
		assertEquals(b, assignmentB.getLeft());
		assertEquals(NumericComparator.EQ, assignmentB.getComparator());
		return true;
	}

	@Test(groups = {"parser", "base"})
	public void quantifierExpression() throws RecognitionException, ImpreciseRepresentationException {
		String testString = "forall (x) : (x > 5b && (exists (c) : (c > x)))";

		Expression expr = parser.parseLogical(testString, new TypeContext(true), vars);

		assertEquals(QuantifierExpression.class, expr.getClass());
		QuantifierExpression allQuantifiedExpr = (QuantifierExpression) expr;
		assertEquals(Quantifier.FORALL, allQuantifiedExpr.getQuantifier());
		assertEquals(1, allQuantifiedExpr.getBoundVariables().size());
		assertEquals(x, allQuantifiedExpr.getBoundVariables().get(0));

		assertEquals(PropositionalCompound.class, allQuantifiedExpr.getBody().getClass());
		PropositionalCompound propCompound = (PropositionalCompound) allQuantifiedExpr.getBody();

		assertEquals(QuantifierExpression.class, propCompound.getRight().getClass());
		QuantifierExpression existQuantifiedExpr = (QuantifierExpression) propCompound.getRight();
		assertEquals(Quantifier.EXISTS, existQuantifiedExpr.getQuantifier());
		assertEquals(1, existQuantifiedExpr.getBoundVariables().size());
		assertEquals(c, existQuantifiedExpr.getBoundVariables().get(0));
	}

	@Test(expectedExceptions = {UndeclaredVariableException.class}, groups = {"parser", "base"})
	public void undeclaredVarInQuantifiedExpression() throws RecognitionException, ImpreciseRepresentationException {
		String testString = "forall (y:sint32) : (exists (a) : (x > 5b && c > 3))";
		Expression expr = parser.parseLogical(testString, new TypeContext(true), vars);
	}

	@Test(expectedExceptions = {RecognitionException.class}, groups = {"parser", "base"})
	public void wrongEQ() throws RecognitionException, ImpreciseRepresentationException {
		String testString = "declare x:sint32 in x = 5";
		Expression expr = parser.parseLogical(testString);
	}
}
