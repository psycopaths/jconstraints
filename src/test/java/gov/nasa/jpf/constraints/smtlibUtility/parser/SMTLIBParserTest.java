package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;
import java.math.BigInteger;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

public class SMTLIBParserTest {

    @Test(groups = {"jsmtlib", "base"})
    public void parsingRoundTripPrimeConesTest() throws IOException, SMTLIBParserException, IParser.ParserException {
        final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_sat_15.smt2");

        assertEquals(problem.variables.size(),
                     15,
                     "There are 15 variables declared in the original SMT-Problem," +
                     "hence 15 variables are expected in the parsed problem");
        for (final Variable v : problem.variables) {
            assertEquals(v.getType(),
                         BuiltinTypes.INTEGER,
                         "They are declared as Int in the SMT-problem," +
                         "which is in jConstraint represented as Integer.");
        }
        assertEquals(problem.assertions.size(), 31, "There are 31 assertions in the original problem.");

        final Expression assertion1 = problem.assertions.get(0);
        assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
        final NumericBooleanExpression convertedAssertion1 = (NumericBooleanExpression) assertion1;
        assertEquals(convertedAssertion1.getLeft().getClass(), Variable.class);
        final Variable left = (Variable) convertedAssertion1.getLeft();
        assertEquals(left.getName(), "x_0");
        assertEquals(convertedAssertion1.getRight().toString(), "0");
        assertEquals(((NumericBooleanExpression) assertion1).getComparator(), NumericComparator.GE);

        final Expression assertion30 = problem.assertions.get(29);
        assertEquals(assertion30.getClass(), NumericBooleanExpression.class);
        final NumericBooleanExpression convertedAssertion30 = (NumericBooleanExpression) assertion30;
        assertEquals(convertedAssertion30.getLeft().getClass(), NumericCompound.class);
        final NumericCompound leftPart = (NumericCompound) convertedAssertion30.getLeft();
        assertEquals(leftPart.getRight().getClass(), NumericCompound.class);
        final NumericCompound testTarget = (NumericCompound) leftPart.getRight();
        assertEquals(testTarget.getRight().getClass(), Variable.class);
        final Variable x14 = (Variable) testTarget.getRight();
        assertEquals(x14.getName(), "x_14");
        assertEquals(testTarget.getLeft().getClass(), UnaryMinus.class);
        final UnaryMinus leftTarget = (UnaryMinus) testTarget.getLeft();
        assertEquals(leftTarget.getNegated().getClass(), Constant.class);
        final Constant v282 = (Constant) leftTarget.getNegated();
        assertEquals(v282.getValue(), BigInteger.valueOf(282));
    }


    @Test(enabled = true, groups = {"jsmtlib", "base"})
    public void parsingRoundTripPRP718Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/prp-7-18.smt2");

        assertEquals(problem.variables.size(), 17);
        assertEquals(problem.assertions.size(), 1);

    }

    @Test(enabled = true, groups = {"jsmtlib", "base"})
    public void parsingKaluza826Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/kaluza_sat_big_826.smt2");

        assertEquals(problem.variables.size(), 69);
        assertEquals(problem.assertions.size(), 71);

    }

    @Test(enabled = true, groups = {"jsmtlib", "base"})
    public void parsingPisa000Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/pisa-000.smt2");

        assertEquals(problem.variables.size(), 4);
        assertEquals(problem.assertions.size(), 3);

    }

    @Test(enabled = false, groups = {"jsmtlib"})
    public void parsingPisa004Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/pisa-004.smt2");

        assertEquals(problem.variables.size(), 10);
        assertEquals(problem.assertions.size(), 6);

    }

    @Test(enabled = false, groups = {"jsmtlib"})
    public void parsingPyEx1Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/pyex_1.smt2");

        assertEquals(problem.variables.size(), 1);
        assertEquals(problem.assertions.size(), 1);

    }
}
