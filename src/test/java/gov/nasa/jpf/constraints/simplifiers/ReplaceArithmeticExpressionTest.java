package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

import java.io.IOException;
import java.util.List;
import java.util.Set;

import static org.testng.Assert.assertEquals;
import static org.testng.AssertJUnit.assertFalse;

public class ReplaceArithmeticExpressionTest {
    private Expression x = Variable.create(BuiltinTypes.SINT32, "x");
    private Expression x1 = Variable.create(BuiltinTypes.SINT32, "x1");

    private Expression c1 = Constant.create(BuiltinTypes.SINT32, 1);
    private Expression c2 = Constant.create(BuiltinTypes.SINT32, 2);
    private Expression c5 = Constant.create(BuiltinTypes.SINT32, 5);
    private Expression xInit = NumericBooleanExpression.create(x, NumericComparator.LT, c2);

    private Expression update = NumericBooleanExpression.create(x1, NumericComparator.EQ, NumericCompound.create(x, NumericOperator.PLUS, c1));
    private Expression guardCheck = NumericBooleanExpression.create(x1, NumericComparator.LT, c5);
    private Expression completeUpdate = ExpressionUtil.and(xInit, update, guardCheck);

    private Expression guardReplaced = NumericBooleanExpression.create(NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.LT, c5);
    private Variable x2 = Variable.create(BuiltinTypes.SINT32, "x2");
    private Constant c4 = Constant.create(BuiltinTypes.SINT32, 20);

    private Expression furtherUpdate = NumericBooleanExpression.create(x2, NumericComparator.EQ, x1);
    private Expression checkOnX2 = NumericBooleanExpression.create(x2, NumericComparator.GE, c4);
    private Expression all = ExpressionUtil.and(completeUpdate, furtherUpdate, checkOnX2);

    private Expression x2GuardReplacement = NumericBooleanExpression.create(NumericCompound.create(x, NumericOperator.PLUS, c1), NumericComparator.GE, c4);

    @Test
    public void simpleReplacementTest() {
        Expression expected = ExpressionUtil.and(xInit, guardReplaced);

        assertEquals(NumericSimplificationUtil.simplify(completeUpdate), expected);
    }

    @Test
    public void noReplacementTest() {
        Expression anotherAssignment = NumericBooleanExpression.create(x1, NumericComparator.EQ, c5);
        Expression expected = ExpressionUtil.and(completeUpdate, anotherAssignment);
        assertEquals(NumericSimplificationUtil.simplify(expected), expected);
    }

    @Test
    public void replacementInChainTest() {
        Expression expected = ExpressionUtil.and(xInit, guardReplaced, x2GuardReplacement);
        assertEquals(NumericSimplificationUtil.simplify(all), expected);
    }

    @Test
    public void replacementInManipulatedChainTest() {
        Variable x3 = Variable.create(BuiltinTypes.SINT32, "x3");
        Expression extension = NumericBooleanExpression.create(x3, NumericComparator.EQ, NumericCompound.create(x2, NumericOperator.PLUS, c5));

        Expression checkX3 = NumericBooleanExpression.create(x3, NumericComparator.LT, c4);
        Expression toSimplify = ExpressionUtil.and(all, checkX3, extension);
        Expression simplified = NumericSimplificationUtil.simplify(toSimplify);

        Set<Variable<?>> variables = ExpressionUtil.freeVariables(simplified);

        assertFalse(variables.contains(x2));
        assertFalse(variables.contains(x1));
        assertFalse(variables.contains(x3));

    }

}
