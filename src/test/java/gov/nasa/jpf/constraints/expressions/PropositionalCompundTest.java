package gov.nasa.jpf.constraints.expressions;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import gov.nasa.jpf.constraints.simplifiers.TailoringVisitor;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashSet;
import org.testng.annotations.Test;

public class PropositionalCompundTest {

  @Test(groups = {"expressions", "base"})
  public void negationTest() {
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

  @Test(
      groups = {"expressions", "base"},
      expectedExceptions = EvaluationException.class)
  public void emptyValuationThrowsError() {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");

    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    pc.evaluate(new Valuation());
  }
}
