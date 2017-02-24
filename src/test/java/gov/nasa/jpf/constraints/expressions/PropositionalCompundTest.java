package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.simplifiers.TailoringVisitor;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.DuplicatingVisitor;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

import java.util.HashSet;

import static org.testng.Assert.assertEquals;

public class PropositionalCompundTest {
    @Test
    public void negationTest(){
        Variable a = Variable.create(BuiltinTypes.BOOL, "a");
        Variable b = Variable.create(BuiltinTypes.BOOL, "b");

        Expression firstNegation = ExpressionUtil.and(new Negation(a), new Negation(b));
        Expression<Boolean> secondNegation = new Negation(firstNegation);

        assertEquals(secondNegation, secondNegation);

        HashSet<Variable<?>> vars = new HashSet<>();
        vars.add(a);
        vars.add(b);

        Expression duplicated = secondNegation.accept(TailoringVisitor.getInstance(), vars);
        assertEquals(duplicated, secondNegation);
    }
}
