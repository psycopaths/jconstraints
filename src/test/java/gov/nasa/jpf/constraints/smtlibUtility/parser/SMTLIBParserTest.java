package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Scanner;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.Helper.parseFile;
import static org.testng.Assert.assertEquals;

public class SMTLIBParserTest {

    @Test
    public void parsingRoundTripPrimeConesTest() throws IOException, SMTLIBParserException, IParser.ParserException {
        SMTProblem problem = parseFile("test_inputs/prime_cone_sat_15.smt2");

        assertEquals(problem.variables.size(), 15,
                "There are 15 variables declared in the original SMT-Problem,"
                        + "hence 15 variables are expected in the parsed problem");
        for (Variable v : problem.variables) {
            assertEquals(v.getType(), BuiltinTypes.INTEGER,
                    "They are declared as Int in the SMT-problem,"
                            + "which is in jConstraint represented as Integer.");
        }
        assertEquals(problem.assertions.size(), 31,
                "There are 31 assertions in the original problem.");

        Expression assertion1 = problem.assertions.get(0);
        assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
        NumericBooleanExpression convertedAssertion1 = (NumericBooleanExpression) assertion1;
        assertEquals(convertedAssertion1.getLeft().getClass(), Variable.class);
        Variable left = (Variable) convertedAssertion1.getLeft();
        assertEquals(left.getName(), "x_0");
        assertEquals(convertedAssertion1.getRight().toString(), "0");
        assertEquals(((NumericBooleanExpression) assertion1).getComparator(), NumericComparator.GE);

        Expression assertion30 = problem.assertions.get(29);
        assertEquals(assertion30.getClass(), NumericBooleanExpression.class);
        NumericBooleanExpression convertedAssertion30 = (NumericBooleanExpression) assertion30;
        assertEquals(convertedAssertion30.getLeft().getClass(), NumericCompound.class);
        NumericCompound leftPart = (NumericCompound) convertedAssertion30.getLeft();
        assertEquals(leftPart.getRight().getClass(),  NumericCompound.class);
        NumericCompound testTarget = (NumericCompound) leftPart.getRight();
        assertEquals(testTarget.getRight().getClass(), Variable.class);
        Variable x14 = (Variable) testTarget.getRight();
        assertEquals(x14.getName(), "x_14");
        assertEquals(testTarget.getLeft().getClass(), UnaryMinus.class);
        UnaryMinus leftTarget = (UnaryMinus) testTarget.getLeft();
        assertEquals(leftTarget.getNegated().getClass(), Constant.class);
        Constant v282 = (Constant) leftTarget.getNegated();
        assertEquals(v282.getValue(), BigInteger.valueOf(282));
    }

    //This test is used for driving the development and the next, that should be enabled an make pass.
    @Test(enabled=false)
    public void parsingRoundTripPRP718Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        SMTProblem problem = parseFile("test_inputs/prp-7-18.smt2");

        assertEquals(problem.variables.size(), 17);
        assertEquals(problem.assertions.size(), 1);

    }
}
