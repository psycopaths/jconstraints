package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

public abstract class AbstractStringExpression extends AbstractExpression<String> {
	@Override
	public Type<String> getType() {
		return BuiltinTypes.STRING;
	}
}
