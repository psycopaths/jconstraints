package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;

import static org.testng.Assert.assertEquals;

public class LetExpressionParsingTest {
    @Test
    public void simpleLetExampleTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        String input = "(declare-fun x () Int)\n" + "(declare-fun y () Int)\n" + "(declare-fun m () Bool)\n" +
                       "(declare-fun n () Bool)\n" + "(declare-fun z () Int)\n" +
                       "(assert (= m (let ((a (= z (+ x 5))) (b (= y (* x 2))) (c (= x 0))) (and a b c (<= y 10)))))" +
                       "\n" + "(assert (= n (and (= z (+ x 5)) (= y (* x 2)) (= x 0) (<= y 10))))\n" +
                       "(assert (= m n))\n" + "(check-sat)\n";

        SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
        assertEquals(problem.variables.size(), 5);
        assertEquals(problem.assertions.size(), 3);

        for (Variable var : problem.variables) {
            if (var.getName().equals("x") || var.getName().equals("y") || var.getName().equals("z")) {
                assertEquals(var.getType(), BuiltinTypes.INTEGER);
            }
            else {
                assertEquals(var.getType(), BuiltinTypes.BOOL);
            }
        }

        Expression assertion1 = problem.assertions.get(0);
        assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
        NumericBooleanExpression cAssertion1 = (NumericBooleanExpression) assertion1;
        assertEquals(cAssertion1.getRight().getClass(), LetExpression.class);
        LetExpression letExpr = (LetExpression) cAssertion1.getRight();
        assertEquals(letExpr.getParameters().size(), 3);
        assertEquals(letExpr.getMainValue().getClass(), PropositionalCompound.class);
    }

    @Test
    public void nestedLetExampleTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        String input = "(declare-fun x () Int)\n" + "(declare-fun y () Int) \n" + "(declare-fun m () Bool) \n" +
                       "(declare-fun n () Bool) \n" + "(declare-fun z () Int) \n" +
                       " (assert (= m (let ((a (= z (+ x 5)))) (let ((b (= y (* x 2))) (c (= x 0))) (and a b c (<= y 10))))))\n" +
                       "(assert (= n (and (= z (+ x 5)) (= y (* x 2)) (= x 0) (<= y 10))))\n" + "(assert (= m n)) \n" +
                       " (check-sat)";

        SMTProblem problem = SMTLIBParser.parseSMTProgram(input);


    }
}
