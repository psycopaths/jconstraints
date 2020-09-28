package gov.nasa.jpf.constraints.smtlib;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import org.smtlib.IParser;
import org.testng.annotations.Test;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

public class QfLiaTest {
	@Test
	public void Problem2Test() throws IOException, SMTLIBParserException, IParser.ParserException, URISyntaxException {
		URL smtFile = QfLiaTest.class.getClassLoader().getResource("problem_2__008.smt2");
		SMTProblem problem = SMTLIBParser.parseSMTProgram(Files.readAllLines(Paths.get(smtFile.toURI()))
															   .stream()
															   .reduce("", (a, b) -> {
																   return b.startsWith(";") ? a : a + b;
															   }));

		NativeZ3Solver z3 = new NativeZ3Solver();
		Valuation model = new Valuation();
		ConstraintSolver.Result jRes = z3.solve(problem.getAllAssertionsAsConjunction(), model);
		assertEquals(jRes, ConstraintSolver.Result.SAT);
		assertTrue(problem.getAllAssertionsAsConjunction().evaluate(model));

	}
}
