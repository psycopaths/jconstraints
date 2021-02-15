package gov.nasa.jpf.constraints.smtlib;

import static org.testng.AssertJUnit.assertEquals;
import static org.testng.AssertJUnit.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import java.io.IOException;
import java.net.URISyntaxException;
import org.smtlib.IParser.ParserException;
import org.testng.annotations.Test;

public class QF_STest {

  @Test
  public void joacoExample1Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("4002_DoSubjectSearch_VxA0.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(jRes, ConstraintSolver.Result.SAT);
    System.out.println(model);
    assertTrue("Model should evaluate to true", expr.evaluateSMT(model));
  }

  @Test
  public void banditfuzzExample1Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("3670_1566478915.37391888518873672772034099_1.smt");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(jRes, ConstraintSolver.Result.UNSAT);
  }

  @Test
  public void banditfuzzExample2Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("3575_1565554544.3963776322835254933674150_1.smt");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(jRes, ConstraintSolver.Result.UNSAT);
  }

  @Test
  public void appscanExample1Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil.loadProblemFromResources("appscan/4_t07.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(jRes, ConstraintSolver.Result.SAT);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }

  @Test
  public void appscanExample2Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/5_t06.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }

  @Test
  public void appscanExample3Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/6_t01.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    SolverContext sc = solver.createContext();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    //sc.add(problem.assertions);
    //sc.push();
    sc.add(expr);
    System.out.println(expr);
    Long start = System.nanoTime();
    ConstraintSolver.Result jRes = sc.solve(model);
    //ConstraintSolver.Result jRes = solver.solve(expr, model);
    Long end = System.nanoTime();
    //sc.pop();
    System.out.println("Solving time: " + (end - start) / 1000000);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluateSMT(model));
  }

  @Test
  public void appscanExample4Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/7_t03.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }

  @Test
  public void appscanExample5Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/8_t02.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }

  @Test
  public void appscanExample6Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/9_t05.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }

  @Test(enabled = false)
  public void appscanExample7Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    //With Z3 4.8.10, this test times out
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/10_t04.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    SolverContext sc = solver.createContext();
    Valuation model = new Valuation();
    sc.add(problem.assertions);
    ConstraintSolver.Result jRes = sc.solve(model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true",
        problem.getAllAssertionsAsConjunction().evaluate(model));
  }

  @Test
  public void appscanExample8Test()
      throws SMTLIBParserException, IOException, ParserException, URISyntaxException {
    SMTProblem problem = LoadingUtil
        .loadProblemFromResources("appscan/11_t08.smt2");
    NativeZ3Solver solver = new NativeZ3Solver();
    Valuation model = new Valuation();
    Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
    System.out.print(expr);
    ConstraintSolver.Result jRes = solver.solve(expr, model);
    assertEquals(ConstraintSolver.Result.SAT, jRes);
    assertTrue("Model should evaluate to true", expr.evaluate(model));
  }
}
