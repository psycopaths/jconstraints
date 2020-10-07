package io.github.tudoaqua.jconstraints.cvc4.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

import java.util.HashMap;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

public class NumericTest {

	CVC4Solver cvc4;
	SolverContext cvc4Context;

	@BeforeMethod
	public void initalize() {
		cvc4 = new CVC4Solver(new HashMap<>());
		cvc4Context = cvc4.createContext();
	}

	@Test
	public void firstTest() {
		Variable x = Variable.create(BuiltinTypes.SINT32, "x");
		Constant c4 = Constant.create(BuiltinTypes.SINT32, 5);
		NumericBooleanExpression expr = NumericBooleanExpression.create(x, NumericComparator.LT, c4);

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(expr, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(expr.evaluate(val));

		expr = NumericBooleanExpression.create(x, NumericComparator.EQ, c4);

		val = new Valuation();
		res = cvc4.solve(expr, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(expr.evaluate(val));
	}

	@Test
	public void secondTest() {
		Variable x = Variable.create(BuiltinTypes.SINT32, "x");
		NumericCompound computation1 =
				NumericCompound.create(x, NumericOperator.MUL, Constant.create(BuiltinTypes.SINT32, 2));
		computation1 = NumericCompound.create(computation1, NumericOperator.PLUS, Constant.create(BuiltinTypes.SINT32, 1));
		CastExpression casted = CastExpression.create(computation1, BuiltinTypes.UINT16);
		casted = CastExpression.create(casted, BuiltinTypes.SINT32);
		BitvectorExpression bvOr =
				BitvectorExpression.create(casted, BitvectorOperator.OR, Constant.create(BuiltinTypes.SINT32, 2));
		BitvectorExpression bvAnd =
				BitvectorExpression.create(bvOr, BitvectorOperator.AND, Constant.create(BuiltinTypes.SINT32, 3));
		NumericBooleanExpression compare =
				NumericBooleanExpression.create(bvAnd, NumericComparator.EQ, Constant.create(BuiltinTypes.SINT32, 3));

		Valuation val = new Valuation();
		ConstraintSolver.Result res = cvc4.solve(compare, val);
		assertEquals(res, ConstraintSolver.Result.SAT);
		assertTrue(compare.evaluate(val));

	}
}
