package gov.nasa.jpf.constraints.type;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.apache.commons.math3.fraction.BigFraction;
import org.testng.annotations.Test;

import static org.testng.Assert.assertFalse;
import static org.testng.Assert.assertTrue;

public class RealTest {

	@Test(groups = {"types", "base"})
	public void simpleRealTest() {
		Variable x = Variable.create(BuiltinTypes.REAL, "x");
		Constant c2_3 = Constant.create(BuiltinTypes.REAL, BigFraction.TWO_THIRDS);
		NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c2_3);
		Valuation valSat = new Valuation();
		valSat.setValue(x, BigFraction.TWO_THIRDS);

		Valuation valUnsat = new Valuation();
		valUnsat.setValue(x, BigFraction.FOUR_FIFTHS);

		assertTrue(expr.evaluate(valSat));
		assertFalse(expr.evaluate(valUnsat));
	}
}
