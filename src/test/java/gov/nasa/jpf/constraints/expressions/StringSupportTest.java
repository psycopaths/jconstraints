package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.UNSAT;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Properties;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class StringSupportTest {

	private NativeZ3Solver solver;

	@BeforeMethod
	public void initialize() {
		Properties conf = new Properties();
		conf.setProperty("symbolic.dp", "z3");
		conf.setProperty("z3.options", "smt.string_solver=seq");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
		solver = (NativeZ3Solver) factory.createSolver();
	}

	@Test
	public void strLenTest() {
		Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable string = Variable.create(BuiltinTypes.STRING, "x1");
		Expression len = StringIntegerExpression.createLength(string);
		len = CastExpression.create(len, BuiltinTypes.SINT32);
		NumericBooleanExpression compLen = NumericBooleanExpression.create(len, NumericComparator.EQ, c5);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(compLen, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		if (res == ConstraintSolver.Result.SAT) {
			assertTrue(compLen.evaluate(val));
		}
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

		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(finalExpr, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		boolean equals = compLen.evaluate(val);
		assertTrue(equals);
	}

	@Test
	public void autoCastStrAtTest() {
		Constant c4 = Constant.create(BuiltinTypes.SINT32, 5);
		Variable strVar = Variable.create(BuiltinTypes.STRING, "string0");
		Expression stringAt = StringCompoundExpression.createAt(strVar, c4);
		Constant stringExpected = Constant.create(BuiltinTypes.STRING, "c");
		stringAt = StringBooleanExpression.createEquals(stringAt, stringExpected);


		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(stringAt, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		boolean equals = (boolean) stringAt.evaluate(val);
		assertTrue(equals);
	}

	@Test
	public void toAndFromIntEvaluationTest() {
		Variable x = Variable.create(BuiltinTypes.STRING, "x");
		Constant c = Constant.create(BuiltinTypes.STRING, "10");
		Expression toInt = StringIntegerExpression.createToInt(x);
		Expression fromInt = StringCompoundExpression.createToString(toInt);
		StringBooleanExpression equals = StringBooleanExpression.createEquals(fromInt, c);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(equals, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(equals.evaluate(val));
	}

	@Test
	public void stringInReTest() {
		Constant c = Constant.create(BuiltinTypes.STRING, "av");
		RegExBooleanExpression rbe = RegExBooleanExpression
				.create(c, RegexOperatorExpression.createAllChar());
		Valuation val = new Valuation();
		ConstraintSolver.Result res = solver.solve(rbe, val);
		assertEquals(res, UNSAT);
	}
}
