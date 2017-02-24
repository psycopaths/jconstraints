package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.BeforeClass;
import org.testng.annotations.Test;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import static org.testng.Assert.assertEquals;

public class ExpressionTailoringUtilTest {
    Variable x = Variable.create(BuiltinTypes.SINT32, "x");
    Variable j = Variable.create(BuiltinTypes.SINT32, "j");
    Variable i = Variable.create(BuiltinTypes.SINT32, "i");

    Constant c1 = Constant.create(BuiltinTypes.SINT32, 10);
    Constant c2 = Constant.create(BuiltinTypes.SINT32, 5);

    Expression assignentIJ = NumericBooleanExpression.create(j,
            NumericComparator.EQ, NumericCompound.create(i, NumericOperator.PLUS, c2));

    Expression constraintI = NumericBooleanExpression.create(i, NumericComparator.LT, c2);
    Expression constraintJ = NumericBooleanExpression.create(j, NumericComparator.LT, c1);

    Expression assignmentXJ = NumericBooleanExpression.create(x, NumericComparator.EQ, j);

    Set<Variable<?>> vars;

    @BeforeClass
    public void setUp(){
        vars = new HashSet<>();
        vars.add(x);
    }

    @Test
    public void disjunctClausesTest(){
        Expression testInput = ExpressionUtil.and(constraintJ, x);
        assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), x);
    }

    @Test
    public void directJoinedTest(){
        Expression testInput = ExpressionUtil.and(assignmentXJ, constraintJ, constraintI);
        Expression expected = ExpressionUtil.and(assignmentXJ, constraintJ);
        assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
    }

    @Test
    public void chainedWithOverlayTest(){
        Expression testInput = ExpressionUtil.and(assignentIJ, constraintI, constraintJ, assignmentXJ);
        Expression expected = ExpressionUtil.and(assignmentXJ, assignentIJ, constraintI, constraintJ);
        assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
    }

    @Test
    public void debuggingWhileLoopTest(){
        Variable a = Variable.create(BuiltinTypes.BOOL, "a");
        Variable b = Variable.create(BuiltinTypes.BOOL, "b");
        Variable c = Variable.create(BuiltinTypes.BOOL, "c");
        Expression part1 = ExpressionUtil.and(new Negation(a), new Negation(b));
        Expression part2 = ExpressionUtil.and(c, new Negation(part1));
        Valuation init = new Valuation();
        init.addEntry(new ValuationEntry<>(a, true));
        init.addEntry(new ValuationEntry<>(b, false));
        assertEquals(ExpressionTailoringUtil.tailor(part2, init.getVariables()),new Negation(part1));
    }
}
