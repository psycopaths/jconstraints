package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

public class LetExpressionTest {
	Variable x = Variable.create(BuiltinTypes.SINT32, "x");
	Constant c = Constant.create(BuiltinTypes.SINT32, 5);
	Expression<Boolean> expr = NumericBooleanExpression.create(x, NumericComparator.GT, c);
	Constant c4 = Constant.create(BuiltinTypes.SINT32, 4);
	LetExpression letExpr = LetExpression.create(x, c4, expr);

	@Test
	public void LetExpressionAcceptsVisitorTest() {
		LetExpressionVisitor visitor  = new LetExpressionVisitor();
		assertEquals(letExpr.accept(visitor, false), letExpr);

	}

	@Test
	public void LetExpressionEvaluation1Test() {
		Valuation val1 = new Valuation();
		val1.setValue(x, 6);

		Valuation val2 = new Valuation();
		val2.setValue(x, 4);

		Valuation val3 = new Valuation();
		val3.setValue(x, 6);

		assertTrue(expr.evaluate(val1));
		assertFalse(letExpr.evaluate(val2));
		assertFalse(letExpr.evaluate(val3));
	}

	@Test
	public void flattenLetExpression1Test(){
		Expression expectedOutcome = NumericBooleanExpression.create(c4, NumericComparator.GT, c);
		assertEquals(letExpr.flattenLetExpression(), expectedOutcome);
	}

	@Test
	public void flattenLetExpression2Test(){
		Variable x1 = Variable.create(BuiltinTypes.SINT32, "x1");
		Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
		Constant c2 = Constant.create(BuiltinTypes.SINT32, 2);
		NumericBooleanExpression partA = NumericBooleanExpression.create(x1, NumericComparator.LE, c4);
		NumericCompound replacement = NumericCompound.create(x2, NumericOperator.PLUS, c2);

		LetExpression expr = LetExpression.create(x1, replacement, partA);

		Expression expectedOutcome = NumericBooleanExpression.create(replacement, NumericComparator.LE, c4);

		assertEquals(expr.flattenLetExpression(), expectedOutcome);

		Variable x3 = Variable.create(BuiltinTypes.BOOL, "x3");
		Expression expr2 = PropositionalCompound.create(x3, LogicalOperator.AND, expr);

		Variable x4 = Variable.create(BuiltinTypes.SINT32, "x4");
		NumericBooleanExpression replacementB = NumericBooleanExpression.create(x4, NumericComparator.GT, c2);
		LetExpression let2 = LetExpression.create(x3, replacementB, expr2);

		Expression expectedOutcome2 = PropositionalCompound.create(replacementB, LogicalOperator.AND, expectedOutcome);

		System.out.println(let2);
		System.out.println(let2.flattenLetExpression());

		assertEquals(let2.flattenLetExpression(), expectedOutcome2);
	}

	public class LetExpressionVisitor extends AbstractExpressionVisitor<Expression, Boolean>{
		@Override
		protected Expression defaultVisit(Expression expression, Boolean data) {
			return expression;
		}
	}
}
