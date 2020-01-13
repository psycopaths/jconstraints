package gov.nasa.jpf.constraints.expressions;

import java.math.BigInteger;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

public abstract class AbstractStringIntegerExpression extends AbstractExpression<BigInteger> {
	@Override
	public Type<BigInteger> getType() {
		return BuiltinTypes.INTEGER;
	}
}
