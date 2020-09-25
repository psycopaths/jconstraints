package gov.nasa.jpf.constraints.type;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import org.testng.annotations.Test;

import static org.testng.Assert.assertEquals;

public class DecimalType {
	@Test(groups = {"basic", "types"})
	public void addRealAsSuperTypeTesT() {
		Type decimal = BuiltinTypes.DECIMAL;
		Type real = BuiltinTypes.REAL;
		assertEquals(decimal.getSuperType(), BuiltinTypes.REAL);
	}
}
