package gov.nasa.jpf.constraints.smtlibUtility.export;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import static org.testng.Assert.assertEquals;

public class Util {
	static void runTest(Expression expr, String expected) {
		SolverContext se;
		ByteArrayOutputStream baos;
		PrintStream ps;
		baos = new ByteArrayOutputStream();
		ps = new PrintStream(baos);
		se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

}
