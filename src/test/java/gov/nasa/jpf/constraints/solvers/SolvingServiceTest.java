package gov.nasa.jpf.constraints.solvers;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserTest;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;

import static org.testng.Assert.assertEquals;

public class SolvingServiceTest {

    @Test(groups = {"testSolver"})
    public void atLeastZ3available(){
        SolvingService service = new SolvingService();
        System.out.println(service.supportedSolvers);
        assert(service.supportedSolvers.contains("Z3") || service.supportedSolvers.contains("NativeZ3"));
    }

    @Test(groups = {"testSolver"})
    public void simpleSolving() {
        SolvingService service = new SolvingService();
        Variable x = Variable.create(BuiltinTypes.SINT32, "x");
        Variable y = Variable.create(BuiltinTypes.SINT32, "y");
        Constant c0 = Constant.create(BuiltinTypes.SINT32, 10);
        Constant c1 = Constant.create(BuiltinTypes.SINT32, 3);

        NumericBooleanExpression expr1 = NumericBooleanExpression.create(x, NumericComparator.EQ, c0);
        NumericBooleanExpression expr2 = NumericBooleanExpression.create(y, NumericComparator.EQ, x);
        NumericBooleanExpression expr3 = NumericBooleanExpression.create(y, NumericComparator.LE, c1);


        ConstraintSolver.Result res = service.solve(ExpressionUtil.and(expr1, expr2, expr3), null);
        assertEquals(res, ConstraintSolver.Result.UNSAT);
    }

    @Test(groups = {"testSolver"})
    public void solveSMTProblemSATTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        SMTProblem problem = SMTLIBParserTest.parseFile("test_inputs/prime_cone_sat_15.smt2");

        SolvingService service = new SolvingService();
        Result res = service.solve(problem);
        assertEquals(res, Result.SAT);
    }

    @Test(groups = {"testSolver"})
    public void solveSMTProblemUNSATTest() throws SMTLIBParserException, IParser.ParserException, IOException {
        SMTProblem problem = SMTLIBParserTest.parseFile("test_inputs/prime_cone_unsat_10.smt2");

        SolvingService service = new SolvingService();
        Result res = service.solve(problem);
        assertEquals(res, Result.UNSAT);
    }
}
