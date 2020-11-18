package gov.nasa.jpf.constraints.smtlibUtility.export;

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.DIV;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MINUS;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MUL;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.PLUS;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.REM;

import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.math.BigInteger;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class NumericTest {
  Variable varInt, varSINT32, varUINT16;
  Constant c15Int, c15SINT32, c15UINT16;

  @BeforeMethod
  public void initialize() {
    varInt = Variable.create(BuiltinTypes.INTEGER, "x");
    varSINT32 = Variable.create(BuiltinTypes.SINT32, "x");
    varUINT16 = Variable.create(BuiltinTypes.UINT16, "x");
    c15Int = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(15));
    c15SINT32 = Constant.create(BuiltinTypes.SINT32, 15);
    c15UINT16 = Constant.create(BuiltinTypes.UINT16, (char) 15);
  }

  @Test(groups = {"basic", "smt-export"})
  public void addIntegerIntegerTest() {
    String expected = "(declare-const x Int)\n(assert (+ x 15))\n";
    NumericCompound expr = NumericCompound.create(varInt, PLUS, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void minusIntegerIntegerTest() {
    String expected = "(declare-const x Int)\n(assert (- x 15))\n";
    NumericCompound expr = NumericCompound.create(varInt, MINUS, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void mulIntegerIntegerTest() {
    String expected = "(declare-const x Int)\n(assert (* x 15))\n";
    NumericCompound expr = NumericCompound.create(varInt, MUL, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void divIntegerIntegerTest() {
    String expected = "(declare-const x Int)\n(assert (div x 15))\n";
    NumericCompound expr = NumericCompound.create(varInt, DIV, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void modIntegerIntegerTest() {
    String expected = "(declare-const x Int)\n(assert (mod x 15))\n";
    NumericCompound expr = NumericCompound.create(varInt, REM, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void addSINT32SINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvadd x #x0000000f))\n";
    NumericCompound expr = NumericCompound.create(varSINT32, PLUS, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void minusSINT32SINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsub x #x0000000f))\n";
    NumericCompound expr = NumericCompound.create(varSINT32, MINUS, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void mulSINT32SINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvmul x #x0000000f))\n";
    NumericCompound expr = NumericCompound.create(varSINT32, MUL, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void divSINT32SINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsdiv x #x0000000f))\n";
    NumericCompound expr = NumericCompound.create(varSINT32, DIV, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void modSINT32SINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsrem x #x0000000f))\n";
    NumericCompound expr = NumericCompound.create(varSINT32, REM, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void addUINT16UINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvadd x #x000f))\n";
    NumericCompound expr = NumericCompound.create(varUINT16, PLUS, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void minusUINT16UINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvsub x #x000f))\n";
    NumericCompound expr = NumericCompound.create(varUINT16, MINUS, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void mulUINT16UINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvmul x #x000f))\n";
    NumericCompound expr = NumericCompound.create(varUINT16, MUL, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void divUINT16UINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvudiv x #x000f))\n";
    NumericCompound expr = NumericCompound.create(varUINT16, DIV, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void modUINT16UINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvurem x #x000f))\n";
    NumericCompound expr = NumericCompound.create(varUINT16, REM, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void ltIntTest() {
    String expected = "(declare-const x Int)\n(assert (< x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, LT, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void leIntTest() {
    String expected = "(declare-const x Int)\n(assert (<= x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, LE, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void gtIntTest() {
    String expected = "(declare-const x Int)\n(assert (> x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, GT, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void geIntTest() {
    String expected = "(declare-const x Int)\n(assert (>= x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, GE, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void notIntTest() {
    String expected = "(declare-const x Int)\n(assert (distinct x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, NE, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void eqIntTest() {
    String expected = "(declare-const x Int)\n(assert (= x 15))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varInt, EQ, c15Int);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void ltSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvslt x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, LT, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void leSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsle x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, LE, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void gtSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsgt x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, GT, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void geSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvsge x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, GE, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void notSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (distinct x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, NE, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void eqSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (= x #x0000000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varSINT32, EQ, c15SINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void ltUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvult x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, LT, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void leUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvule x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, LE, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void gtUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvugt x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, GT, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void geUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvuge x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, GE, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void notUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (distinct x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, NE, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void eqUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (= x #x000f))\n";
    NumericBooleanExpression expr = NumericBooleanExpression.create(varUINT16, EQ, c15UINT16);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void unaryMinusIntTest() {
    String expected = "(declare-const x Int)\n(assert (- x))\n";
    UnaryMinus expr = UnaryMinus.create(varInt);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void unaryMinusSINT32Test() {
    String expected = "(declare-const x (_ BitVec 32))\n(assert (bvneg x))\n";
    UnaryMinus expr = UnaryMinus.create(varSINT32);
    Util.runTest(expr, expected);
  }

  @Test(groups = {"basic", "smt-export"})
  public void unaryMinusUINT16Test() {
    String expected = "(declare-const x (_ BitVec 16))\n(assert (bvneg x))\n";
    UnaryMinus expr = UnaryMinus.create(varUINT16);
    Util.runTest(expr, expected);
  }
}
