package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

import static org.testng.AssertJUnit.assertFalse;

public class ExpressionUtilTest {

    @Test
    public void mustReplaceEveryVariableTest() {
        Variable x = Variable.create(BuiltinTypes.SINT32, "x");

        Constant c20 = Constant.create(BuiltinTypes.SINT32, 20);

        Variable x1 = Variable.create(BuiltinTypes.SINT32, "x1");
        Constant c1 = Constant.create(BuiltinTypes.SINT32, 1);

        Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
        Constant c0 = Constant.create(BuiltinTypes.SINT32, 0);

        Expression lessThan20 = NumericBooleanExpression.create(x, NumericComparator.LE, c20);
        Expression updatex1 = NumericBooleanExpression.create(x1, NumericComparator.EQ, NumericCompound.create(x, NumericOperator.PLUS, c1));
        Expression x1LessThan20 = NumericBooleanExpression.create(x1, NumericComparator.LE, c20);
        Expression updatex2 = NumericBooleanExpression.create(x2, NumericComparator.EQ, NumericCompound.create(x1, NumericOperator.PLUS, c1));
        Expression x2LessThan20 = NumericBooleanExpression.create(x2, NumericComparator.LE, c20);

        Expression init = NumericBooleanExpression.create(x, NumericComparator.EQ, c0);

        Expression complete = ExpressionUtil.and(lessThan20, updatex1, x1LessThan20, updatex2, x2LessThan20, init);
        Expression simplified = ExpressionUtil.simplifyAgressiv(complete);
        assertFalse(ExpressionUtil.freeVariables(simplified).contains(x));
        assertFalse(ExpressionUtil.freeVariables(simplified).contains(x1));
        assertFalse(ExpressionUtil.freeVariables(simplified).contains(x2));
    }
}
