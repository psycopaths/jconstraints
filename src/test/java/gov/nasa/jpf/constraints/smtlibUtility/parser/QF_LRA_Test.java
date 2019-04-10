package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;

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

    @Test(enabled = false)
    public void realParsingCountBy2Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/_count_by_2.i_3_2_2.bpl_1.smt2");
        final Expression assertStmt = problem.assertions.get(0);
        assertEquals(assertStmt.getClass(), PropositionalCompound.class);
        assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
    }
}
