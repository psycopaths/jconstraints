package gov.nasa.jpf.constraints.type;

import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

public class BitvectorTypeTest {

  @Test
  public void firstTest() throws ImpreciseRepresentationException {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    NumericCompound computation1 =
        NumericCompound.create(x, NumericOperator.MUL, Constant.create(BuiltinTypes.SINT32, 2));
    computation1 =
        NumericCompound.create(
            computation1, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 1));
    CastExpression casted = CastExpression.create(computation1, BuiltinTypes.UINT16);
    casted = CastExpression.create(casted, BuiltinTypes.SINT32);
    BitvectorExpression bvOr =
        BitvectorExpression.create(
            casted, BitvectorOperator.OR, Constant.create(BuiltinTypes.SINT32, 2));
    BitvectorExpression bvAnd =
        BitvectorExpression.create(
            bvOr, BitvectorOperator.AND, Constant.create(BuiltinTypes.SINT32, 3));
    NumericBooleanExpression compare =
        NumericBooleanExpression.create(
            bvAnd, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3));

    Valuation val = new Valuation();
    val.setParsedValue(x, "3");
    assertTrue(compare.evaluate(val));
  }
}
