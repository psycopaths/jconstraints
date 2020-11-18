package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.math.BigInteger;

public abstract class AbstractStringIntegerExpression extends AbstractExpression<BigInteger> {
  @Override
  public Type<BigInteger> getType() {
    return BuiltinTypes.INTEGER;
  }
}
