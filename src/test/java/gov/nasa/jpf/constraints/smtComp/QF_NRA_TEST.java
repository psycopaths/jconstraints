package gov.nasa.jpf.constraints.smtComp;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import org.smtlib.IParser;
import org.testng.annotations.Test;


public class QF_NRA_TEST {
    @Test
    public void runGen09Test() throws SMTLIBParserException, IParser.ParserException, IOException {

        final SMTProblem problem = ResourceParsingHelper.parseResourceFile("test_inputs/gen-09.smt2");
        final NativeZ3Solver solver = new NativeZ3Solver();
        final Valuation val = new Valuation();
        final ConstraintSolver.Result res = solver.solve(problem.getAllAssertionsAsConjunction(), val);
        assertEquals(res, SAT);
        assertEquals(val.getVariables().size(), 2);
    }
}
