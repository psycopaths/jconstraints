package gov.nasa.jpf.constraints.solvers;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

/*
 * All test cases in this class are supposed to be executed for testing
 * avilability of solvers. As this test can not be run by jConstraints
 * alone, they are in a special test group.
 * @TODO: make a build target for running this kind of tests.
 *
 * @author: Malte Mues (@mmuesly)
 */

public class SolvingServiceTest {

    @Test(groups = {"testSolver"})
    public void atLeastZ3available() {
        final SolvingService service = new SolvingService();
        System.out.println(service.supportedSolvers);
        assert (service.supportedSolvers.contains("Z3") || service.supportedSolvers.contains("NativeZ3"));
    }

    @Test(groups = {"testSolver"})
    public void simpleSolving() {
        final SolvingService service = new SolvingService();
        final Variable x = Variable.create(BuiltinTypes.SINT32, "x");
        final Variable y = Variable.create(BuiltinTypes.SINT32, "y");
        final Constant c0 = Constant.create(BuiltinTypes.SINT32, 10);
        final Constant c1 = Constant.create(BuiltinTypes.SINT32, 3);

        final NumericBooleanExpression expr1 = NumericBooleanExpression.create(x, NumericComparator.EQ, c0);
        final NumericBooleanExpression expr2 = NumericBooleanExpression.create(y, NumericComparator.EQ, x);
        final NumericBooleanExpression expr3 = NumericBooleanExpression.create(y, NumericComparator.LE, c1);


        final ConstraintSolver.Result res = service.solve(ExpressionUtil.and(expr1, expr2, expr3), null);
        assertEquals(res, ConstraintSolver.Result.UNSAT);
    }

    @Test(groups = {"testSolver"})
    public void solveSMTProblemSATTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_sat_15.smt2");

        final SolvingService service = new SolvingService();
        final Result res = service.solve(problem);
        assertEquals(res, Result.SAT);
    }

    @Test(groups = {"testSolver"})
    public void solveSMTProblemUNSATTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_unsat_10.smt2");

        final SolvingService service = new SolvingService();
        final Result res = service.solve(problem);
        assertEquals(res, Result.UNSAT);
    }

    @Test(groups = {"testSolver"})
    public void solveGen09Test() throws SMTLIBParserException, IParser.ParserException, IOException {
        final SMTProblem problem = parseResourceFile("test_inputs/gen-09.smt2");

        final SolvingService service = new SolvingService();
        final Result res = service.solve(problem);
        assertEquals(res, Result.SAT);
    }
}
