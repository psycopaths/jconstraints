package gov.nasa.jpf.constraints.simplifiers;

import com.sun.org.apache.xpath.internal.operations.Bool;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.flattenedExpression.FlatBooleanExpression;
import gov.nasa.jpf.constraints.flattenedExpression.FlattenedExpressionVisitior;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.testng.annotations.Test;

import java.io.IOException;

import static org.testng.Assert.assertEquals;

public class DuplicationRemoverTest {

    Variable<Integer> x = Variable.create(BuiltinTypes.SINT32, "x");
    Constant<Integer> c1 = Constant.create(BuiltinTypes.SINT32, 3);
    Variable<Integer> x2 = Variable.create(BuiltinTypes.SINT32, "y");
    Constant<Integer> c2 = Constant.create(BuiltinTypes.SINT32, 4);
    Expression lessThanExpression = NumericBooleanExpression.create(x, NumericComparator.LT, c1);
    Expression greaterThan = new NumericBooleanExpression(x2, NumericComparator.LT, c2);
    Expression addition = new NumericCompound(x2, NumericOperator.PLUS, c2);
    Expression assignment = new NumericBooleanExpression(x, NumericComparator.EQ, c2);

    @Test(groups = {"simplifiers", "base"})
    public void simpleDuplicationTest() throws IOException {
        Expression<Boolean> longerExpression = ExpressionUtil.and(lessThanExpression, lessThanExpression, lessThanExpression, lessThanExpression);

        Expression simplified = ExpressionUtil.simplify(longerExpression);

        Expression<Boolean> withoutDuplication = ExpressionUtil.simplifyAgressiv(longerExpression);

        assertEquals(withoutDuplication, lessThanExpression);
    }

    @Test(groups = {"simplifiers", "base"})
    public void simpleDuplication2Test() {
        Expression<Boolean> longerExpression = ExpressionUtil.and(greaterThan, lessThanExpression);
        longerExpression = ExpressionUtil.or(longerExpression, greaterThan);

        Expression simplified = ExpressionUtil.simplifyAgressiv(longerExpression);
        assertEquals(simplified.toString(), longerExpression.toString());
    }

    @Test(groups = {"simplifiers", "base"})
    public void simpleDuplicationOrTest() {
        Expression firstPart = ExpressionUtil.or(assignment, assignment);
        Expression secondPart = ExpressionUtil.and(lessThanExpression, greaterThan, lessThanExpression);
        Expression<Boolean> thirdPart = ExpressionUtil.and(new Negation(firstPart), new Negation(secondPart));

        Expression expected = ExpressionUtil.and(new Negation(assignment),
                                                 new Negation(ExpressionUtil.and(lessThanExpression, greaterThan)));

        Expression flat = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
        assertEquals(flat.getChildren()[0].getClass(), Negation.class);
        assertEquals(((Negation) flat.getChildren()[0]).getNegated().getClass(), FlatBooleanExpression.class);

        Expression<Boolean> first = thirdPart.accept(FlatExpressionVisitor.getInstance(), null);
        Expression second = first.accept(SimplificationVisitor.getInstance(), null);

        assertEquals(second, expected);
    }

}
