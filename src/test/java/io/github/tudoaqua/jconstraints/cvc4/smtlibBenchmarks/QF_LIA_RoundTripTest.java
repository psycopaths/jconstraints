package io.github.tudoaqua.jconstraints.cvc4.smtlibBenchmarks;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

public class QF_LIA_RoundTripTest {

	@Test
	public void Problem2Test() throws IOException, SMTLIBParserException, IParser.ParserException, URISyntaxException {
		URL smtFile = QF_LIA_RoundTripTest.class.getClassLoader().getResource("problem_2__008.smt2");
		SMTProblem problem = SMTLIBParser.parseSMTProgram(Files.readAllLines(Paths.get(smtFile.toURI()))
															   .stream()
															   .reduce("", (a, b) -> {
																   return b.startsWith(";") ? a : a + b;
															   }));

		CVC4Solver cvc4 = new CVC4Solver(new HashMap<>());
		SolverContext ctx = cvc4.createContext();
		Valuation model = new Valuation();
		Expression<Boolean> expr = problem.getAllAssertionsAsConjunction();
		ctx.add(expr);
		ConstraintSolver.Result jRes = ctx.solve(model);
		assertEquals(jRes, ConstraintSolver.Result.SAT);
		assertTrue(problem.getAllAssertionsAsConjunction().evaluate(model));

	}
}
