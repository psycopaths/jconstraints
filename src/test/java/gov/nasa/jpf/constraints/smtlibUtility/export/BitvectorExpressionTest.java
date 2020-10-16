package gov.nasa.jpf.constraints.smtlibUtility.export;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import static org.testng.Assert.assertEquals;

public class BitvectorExpressionTest {
	Variable x;
	Constant c0SINT32;
	SolverContext se;

	ByteArrayOutputStream baos;
	PrintStream ps;

	@BeforeMethod
	public void initialize() {
		x = Variable.create(BuiltinTypes.SINT32, "X");
		c0SINT32 = Constant.create(BuiltinTypes.SINT32, 0);

		baos = new ByteArrayOutputStream();
		ps = new PrintStream(baos);

		se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
	}

	@Test
	public void BVAndTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvand X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.AND, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVOrTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvor X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.OR, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVXorTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvxor X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.XOR, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVShiftLTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvshl X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTL, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVShiftRTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvashr X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTR, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVShiftURTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvlshr X #x00000000))\n";

		BitvectorExpression expr = BitvectorExpression.create(x, BitvectorOperator.SHIFTUR, c0SINT32);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVNegationTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvnot X))\n";

		BitvectorNegation expr = BitvectorNegation.create(x);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}

	@Test
	public void BVUnaryMinusTest() {
		String expected = "(declare-const X (_ BitVec 32))\n(assert (bvneg X))\n";

		UnaryMinus expr = UnaryMinus.create(x);
		se.add(expr);
		String output = baos.toString();
		assertEquals(output, expected);
	}
}
