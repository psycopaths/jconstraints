package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

public class StringExpressionsTest {

	@Test
	public void toLowerEvaluationTest() {
		Variable var = Variable.create(BuiltinTypes.STRING, "x");
		Constant cU = Constant.create(BuiltinTypes.STRING, "UpperCase");
		Constant target = Constant.create(BuiltinTypes.STRING, "uppercase");

		StringBooleanExpression part1 = StringBooleanExpression.createEquals(var, cU);
		StringCompoundExpression upper = StringCompoundExpression.createToLower(var);
		StringBooleanExpression part2 = StringBooleanExpression.createEquals(upper, target);
		PropositionalCompound complete = PropositionalCompound.create(part1, AND, part2);


		Valuation val = new Valuation();
		val.setValue(var, "UpperCase");
		assertTrue(complete.evaluate(val));

		val.setValue(var, "upperCase");
		assertFalse(complete.evaluate(val));
	}

	@Test
	public void toAndFromIntEvaluationTest() {
		Variable x = Variable.create(BuiltinTypes.STRING, "x");
		Constant c = Constant.create(BuiltinTypes.STRING, "C");
		Expression toInt = StringIntegerExpression.createToInt(x);
		Expression fromInt = StringCompoundExpression.createToString(toInt);
		StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, x);

		Valuation val = new Valuation();
		val.setValue(x, "C");
		assertTrue(equals.evaluate(val));
	}

	@Test
	public void equalsTestSpecialChars() {
		Variable x = Variable.create(BuiltinTypes.STRING, "_string1");
		Constant c = Constant.create(BuiltinTypes.STRING, "W\f49-44-44");
		StringBooleanExpression equals = StringBooleanExpression.createEquals(x, c);

		Valuation val = new Valuation();
		val.setValue(x, "W\f49-44-44");
		
		assertTrue(equals.evaluate(val));
	}
}
