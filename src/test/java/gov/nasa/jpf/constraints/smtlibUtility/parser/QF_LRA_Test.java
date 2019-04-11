package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.smtlib.CharSequenceReader;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.loadResource;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

public class QF_LRA_Test {
    @Test
    public void realParsingbignum_lra1Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/bignum_lra1.smt2");
        final Expression assertStmt = problem.assertions.get(0);
        assertEquals(assertStmt.getClass(), PropositionalCompound.class);
        assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
    }

    @Test
    public void realParsingCountBy2Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/_count_by_2.i_3_2_2.bpl_1.smt2");
        final Expression assertStmt = problem.assertions.get(0);
        assertEquals(problem.getAllAssertionsAsConjunction().getClass(), PropositionalCompound.class);
        assertEquals(problem.getAllAssertionsAsConjunction().getType(), BuiltinTypes.BOOL);
        assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
    }

    @Test
    public void realParsingIntersectionExampleTest() throws
            SMTLIBParserException,
            IParser.ParserException,
            IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/intersection-example.smt2");
        final Expression assertStmt = problem.assertions.get(0);
        assertEquals(problem.getAllAssertionsAsConjunction().getClass(), Negation.class);
        assertEquals(problem.getAllAssertionsAsConjunction().getType(), BuiltinTypes.BOOL);
        assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
    }

    /*
     * For some reason, we have encountered a problem, whenever the size of the input buffer used by the
     * CharSequenceReader
     * is less than the size of the Stirng feed ot the String Builder.
     * @FIXME: Investigate further and fix in jSMTLIB interaction with JDK.
     */
    @Test(enabled = false)
    public void readingCountBy2Test() throws IOException, InterruptedException {
        final String targetResource = "test_inputs/_count_by_2.i_3_2_2.bpl_1.smt2";
        final StringBuilder b = new StringBuilder();
        final BufferedReader reader = new BufferedReader(new FileReader(loadResource(targetResource)));
        reader.lines().forEach(e -> b.append(e));

        final String fileContent = b.toString();

        System.out.println("File size: " + fileContent.length());
        //        final CharSequenceReader charReader = new CharSequenceReader(new StringReader(fileContent),
        //                                                                     fileContent.length(),
        //                                                                     100,
        //                                                                     2);

        final CharSequenceReader charReader = new CharSequenceReader(new StringReader(fileContent));

        final BufferedReader reader2 = new BufferedReader(new StringReader(fileContent));
        final String res = reader2.lines().reduce("", (a, e) -> a += e);

        for (int i = 0; i < fileContent.length(); i++) {
            assertEquals(res.charAt(i),
                         fileContent.charAt(i),
                         "The chars should be equals but diverged at i=" + i + " got: " +
                         Character.getNumericValue(res.charAt(i)));
        }

        for (int i = 0; i < fileContent.length(); i++) {
            assertEquals(charReader.charAt(i),
                         fileContent.charAt(i),
                         "The chars should be equals but diverged at i=" + i + " got: " +
                         Character.getNumericValue(charReader.charAt(i)));
        }
    }
}
