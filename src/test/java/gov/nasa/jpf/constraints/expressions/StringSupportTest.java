package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

import java.util.Properties;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

public class StringSupportTest {

	@Test
	public void strLenTest() {
		Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable string = Variable.create(BuiltinTypes.STRING, "x1");
		Expression len = StringIntegerExpression.createLength(string);
		len = CastExpression.create(len, BuiltinTypes.SINT32);
		NumericBooleanExpression compLen = NumericBooleanExpression.create(len, NumericComparator.EQ, c5);

		Properties conf = new Properties();
		conf.setProperty("symbolic.dp", "z3");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
		NativeZ3Solver solver = (NativeZ3Solver) factory.createSolver();
		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(compLen, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(compLen.evaluate(val));
	}

	@Test
	public void strLen2Test() {
		Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable string = Variable.create(BuiltinTypes.STRING, "x1");
		Expression len = StringIntegerExpression.createLength(string);
		len = CastExpression.create(len, BuiltinTypes.SINT32);
		NumericBooleanExpression compLen = NumericBooleanExpression.create(len, NumericComparator.EQ, c5);

		Constant<String> cHallo = Constant.create(BuiltinTypes.STRING, "Hallo");
		StringBooleanExpression strEq = StringBooleanExpression.createEquals(string, cHallo);

		Expression finalExpr = PropositionalCompound.create(compLen, LogicalOperator.AND, strEq);

		Properties conf = new Properties();
		conf.setProperty("symbolic.dp", "z3");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
		NativeZ3Solver solver = (NativeZ3Solver) factory.createSolver();
		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(finalExpr, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		boolean equals = compLen.evaluate(val);
		assertTrue(equals);
	}
}
