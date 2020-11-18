package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.util.Set;
import org.smtlib.IParser;
import org.testng.annotations.Test;

/*
 * All test cases in this test case are taken from the QF_NRA section
 * of the SMT competition 2018.
 *
 * @author Malte Mues (@mmuesly)
 */
public class QF_NRA_Test {
  @Test(groups = {"jsmtlib", "base"})
  public void realParsingGen09Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/gen-09.smt2");

    final Expression singleExpr = problem.getAllAssertionsAsConjunction();
    final Set<Variable<?>> vars = ExpressionUtil.freeVariables(singleExpr);

    for (final Variable v : vars) {
      assertEquals(v.getType(), BuiltinTypes.DECIMAL);
    }
    final Expression firstAssertion = problem.assertions.get(0);
    assertEquals(firstAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedFirstAssertion = (NumericBooleanExpression) firstAssertion;
    assertEquals(castedFirstAssertion.getComparator(), NumericComparator.EQ);

    final Expression secondAssertion = problem.assertions.get(1);
    assertEquals(secondAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedSecondAssertion =
        (NumericBooleanExpression) secondAssertion;
    assertEquals(castedSecondAssertion.getComparator(), NumericComparator.EQ);

    final Expression thirdAssertion = problem.assertions.get(2);
    assertEquals(thirdAssertion.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedThirdAssertion = (NumericBooleanExpression) thirdAssertion;
    assertEquals(castedThirdAssertion.getComparator(), NumericComparator.GT);
    assertEquals(((Variable) castedThirdAssertion.getLeft()).getName(), "b");
    assertEquals(((Variable) castedThirdAssertion.getRight()).getName(), "a");
  }

  @Test(groups = {"jsmtlib", "base"})
  public void realParsingGen14Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/gen-14.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression castedAssertStmt = (NumericBooleanExpression) assertStmt;
    assertEquals(castedAssertStmt.getRight().getClass(), UnaryMinus.class);
    assertEquals(castedAssertStmt.getRight().getType(), BuiltinTypes.DECIMAL);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void realParsingMgc02Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/mgc_02.smt2");
    assertEquals(problem.assertions.size(), 1);
    final Expression assertion = problem.assertions.get(0);
    assertEquals(assertion.getType(), BuiltinTypes.BOOL);

    final Set<Variable<?>> vars = ExpressionUtil.freeVariables(assertion);
    for (final Variable v : vars) {
      assertEquals(v.getType(), BuiltinTypes.DECIMAL);
    }
  }
}
