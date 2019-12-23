package gov.nasa.jpf.constraints.expressions;

import java.util.Properties;

import org.testng.annotations.Test;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;


public class RegexTest {
	public static void main(String[]args) {
		RegexTest t = new RegexTest();
		t.testToString();
	}
	public void testToString() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "Z3");
	    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	    ConstraintSolver solver = factory.createSolver();
	
	    SolverContext ctx = solver.createContext();

		Constant<String> hello = Constant.create(BuiltinTypes.REGEX, "Hello");

		Constant<String> hi = Constant.create(BuiltinTypes.STRING, "Hello");

		RegExBooleanExpression test = RegExBooleanExpression.create(hello, hi);

		Valuation val = new Valuation();
        ConstraintSolver.Result result = solver.solve(test, val);
        System.out.println(result);
        System.out.println(val);
        
	}


	
}
