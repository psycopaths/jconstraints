package gov.nasa.jpf.constraints.smtlibUtility.export;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class CastExpressionTest {
  SolverContext se;
  ByteArrayOutputStream baos;
  PrintStream ps;

  @BeforeMethod
  public void initialize() {
    baos = new ByteArrayOutputStream();
    ps = new PrintStream(baos);
    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
  }

  @Test
  public void castSINT32IntegerTest() {
    String expected =
        "(declare-const X (_ BitVec 32))\n"
            + "(assert (ite (bvslt X #x00000000) (- (bv2nat X)) (bv2nat X)))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT32, "X"), BuiltinTypes.INTEGER);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test
  public void castIntegerSINT32Test() {
    String expected =
        "(declare-const X Int)\n"
            + "(assert (ite (< X 0) (bvneg ((_ nat2bv 32) X)) ((_ nat2bv 32) X)))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.INTEGER, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test
  public void castIntegerSINT8Test() {
    String expected =
        "(declare-const X Int)\n(assert (ite (< X 0) (bvneg ((_ nat2bv 8) X)) ((_ nat2bv 8) X)))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.INTEGER, "X"), BuiltinTypes.SINT8);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test
  public void castSINT8SINT32Test() {
    String expected = "(declare-const X (_ BitVec 8))\n(assert ((_ sign_extend 24) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT8, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test
  public void castSINT8UINT16Test() {
    String expected = "(declare-const X (_ BitVec 8))\n(assert ((_ sign_extend 8) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.SINT8, "X"), BuiltinTypes.UINT16);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }

  @Test
  public void castUINT16SINT32Test() {
    String expected = "(declare-const X (_ BitVec 16))\n(assert ((_ zero_extend 16) X))\n";
    CastExpression expr =
        CastExpression.create(Variable.create(BuiltinTypes.UINT16, "X"), BuiltinTypes.SINT32);
    se.add(expr);
    String output = baos.toString();
    assertEquals(output, expected);
  }
}
