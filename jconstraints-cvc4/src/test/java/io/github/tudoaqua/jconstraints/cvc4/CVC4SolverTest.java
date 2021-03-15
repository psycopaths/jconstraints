/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package io.github.tudoaqua.jconstraints.cvc4;

import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.LE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.NE;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.MINUS;
import static gov.nasa.jpf.constraints.expressions.NumericOperator.PLUS;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.Result;
import edu.stanford.CVC4.Result.Sat;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import edu.stanford.CVC4.SortType;
import edu.stanford.CVC4.Type;
import edu.stanford.CVC4.vectorExpr;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NamedSort;
import gov.nasa.jpf.constraints.types.TypeContext;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.apache.commons.math3.fraction.BigFraction;
import org.testng.SkipException;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class CVC4SolverTest extends AbstractCVC4Test {
  ExprManager em;
  SmtEngine smt;

  @BeforeMethod
  public void initializeEngine() {
    try {
      em = new ExprManager();
      smt = new SmtEngine(em);
    } catch (UnsatisfiedLinkError e) {
      throw new SkipException("No native CVC4 support", e);
    }
    smt.setOption("produce-models", new SExpr(true));
  }

  @Test
  public void linearArith() {
    smt.setLogic("QF_LIRA"); // Set the logic

    // Types
    Type real = em.realType();
    Type integer = em.integerType();

    // Variables
    Expr x = em.mkVar("x", integer);
    Variable jX = Variable.create(BuiltinTypes.INTEGER, "x");
    Expr a = em.mkVar("a", real);
    Variable jA = Variable.create(BuiltinTypes.REAL, "a");
    Expr b = em.mkVar("b", integer);
    Variable jB = Variable.create(BuiltinTypes.INTEGER, "b");

    // Constants
    Expr three = em.mkConst(new Rational(3));
    Constant c3 = Constant.createCasted(BuiltinTypes.REAL, new BigFraction(3));
    Expr nullC = em.mkConst(new Rational(0));
    Constant c0 = Constant.createCasted(BuiltinTypes.REAL, BigFraction.ZERO);
    Expr two_thirds = em.mkConst(new Rational(2, 3));
    Constant c2_3 = Constant.create(BuiltinTypes.REAL, BigFraction.TWO_THIRDS);

    TypeContext typeContext = new TypeContext();
    typeContext.addBuiltinTypes();

    // Terms
    Expr plus = em.mkExpr(Kind.PLUS, a, b);
    Expression jPlus = NumericCompound.createCompatible(jA, PLUS, jB, typeContext);

    Expr diff = em.mkExpr(Kind.MINUS, a, x);
    Expression jDiff = NumericCompound.createCompatible(jA, MINUS, jX, typeContext);

    // Formulas
    Expr x_geq_3y = em.mkExpr(Kind.EQUAL, x, plus);
    Expression jX_geq_3y = NumericBooleanExpression.create(jX, EQ, jPlus);

    Expr x_leq_y = em.mkExpr(Kind.GT, a, nullC);
    Expression jX_leq_y = NumericBooleanExpression.create(jA, GT, c0);

    Expr neg2_lt_x = em.mkExpr(Kind.GT, b, nullC);
    Expression jNeg2_lt_x = NumericBooleanExpression.create(jB, GT, c0);

    Expr assumptions = em.mkExpr(Kind.AND, x_geq_3y, x_leq_y);
    Expression<Boolean> jAssumptions = PropositionalCompound.create(jX_geq_3y, AND, jX_leq_y);

    assumptions = em.mkExpr(Kind.AND, assumptions, neg2_lt_x);
    jAssumptions = PropositionalCompound.create(jAssumptions, AND, jNeg2_lt_x);
    smt.assertFormula(assumptions);
    cvc4Context.add(jAssumptions);
    Result resNative = smt.checkSat();
    ConstraintSolver.Result resJConstraints = cvc4Context.isSatisfiable(jAssumptions);
    assertEquals(
        resNative.isSat().toString().toLowerCase(), resJConstraints.toString().toLowerCase());

    smt.push();
    cvc4Context.push();

    Expr diff_leq_two_thirds = em.mkExpr(Kind.LEQ, diff, two_thirds);
    Result resCVC4 = smt.checkSat(diff_leq_two_thirds);
    assertEquals(resCVC4.toString().toLowerCase(), Sat.SAT.toString().toLowerCase());
    assertEquals(
        resCVC4.toString().toLowerCase(), cvc4Context.isSatisfiable().toString().toLowerCase());
    Valuation model = new Valuation();
    cvc4Context.solve(model);
    Valuation model2 = new Valuation();
    cvc4.solve(jAssumptions, model2);
    assertTrue(jAssumptions.evaluate(model));
    assertTrue(jAssumptions.evaluate(model2));
    assertEquals(model, model2);

    smt.push();
    cvc4Context.push();

    assertEquals(
        smt.checkSat(em.mkConst(true)).toString().toLowerCase(), Sat.SAT.toString().toLowerCase());
    assertEquals(ConstraintSolver.Result.SAT, cvc4Context.isSatisfiable(ExpressionUtil.TRUE));

    smt.pop();
    cvc4Context.pop();
  }

  @Test
  public void bitVectorsTest() {
    Result.Entailment expect, actual;
    smt.setLogic("QF_BV");

    // The following example has been adapted from the book A Hacker's Delight by
    // Henry S. Warren.
    //
    // Given a variable x that can only have two values, a or b. We want to
    // assign to x a value other than the current one. The straightforward code
    // to do that is:
    //
    // (0) if (x == a ) x = b;
    //    else x = a;
    //
    // Two more efficient yet equivalent methods are:
    //
    // (1) x = a xor b xor x;
    //
    // (2) x = a + b - x;
    //
    // We will use CVC4 to prove that the three pieces of code above are all
    // equivalent by encoding the problem in the bit-vector theory.

    // Creating a bit-vector type of width 32
    Type bitvector32 = em.mkBitVectorType(32);

    // Variables
    Expr x = em.mkVar("x", bitvector32);
    Variable jX = Variable.create(BuiltinTypes.SINT32, "x");

    Expr a = em.mkVar("a", bitvector32);
    Variable jA = Variable.create(BuiltinTypes.SINT32, "A");

    Expr b = em.mkVar("b", bitvector32);
    Variable jB = Variable.create(BuiltinTypes.SINT32, "B");

    // First encode the assumption that x must be equal to a or b
    Expr x_eq_a = em.mkExpr(Kind.EQUAL, x, a);
    NumericBooleanExpression jX_qe_a = NumericBooleanExpression.create(jX, EQ, jA);

    Expr x_eq_b = em.mkExpr(Kind.EQUAL, x, b);
    NumericBooleanExpression jX_eq_b = NumericBooleanExpression.create(jX, EQ, jB);

    Expr assumption = em.mkExpr(Kind.OR, x_eq_a, x_eq_b);
    PropositionalCompound jAssumption =
        PropositionalCompound.create(jX_qe_a, LogicalOperator.OR, jX_eq_b);

    // Assert the assumption
    smt.assertFormula(assumption);
    cvc4Context.add(jAssumption);

    // Introduce a new variable for the new value of x after assignment.
    Expr new_x = em.mkVar("new_x", bitvector32); // x after executing code (0)
    Variable jNewX = Variable.create(BuiltinTypes.SINT32, "newX");

    Expr new_x_ = em.mkVar("new_x_", bitvector32); // x after executing code (1) or (2)
    Variable jNewX_ = Variable.create(BuiltinTypes.SINT32, "newX_");

    // Encoding code (0)
    // new_x = x == a ? b : a;
    Expr ite = em.mkExpr(Kind.ITE, x_eq_a, b, a);
    Expression jIte = IfThenElse.create(jX_qe_a, jB, jA);
    Expr assignment0 = em.mkExpr(Kind.EQUAL, new_x, ite);
    NumericBooleanExpression jAssignement0 = NumericBooleanExpression.create(jNewX, EQ, jIte);

    // Assert the encoding of code (0)
    smt.assertFormula(assignment0);
    cvc4Context.add(jAssignement0);

    smt.push();
    cvc4Context.push();

    // Encoding code (1)
    // new_x_ = a xor b xor x
    Expr a_xor_b_xor_x = em.mkExpr(Kind.BITVECTOR_XOR, a, b, x);
    BitvectorExpression jAxorBxorX =
        BitvectorExpression.create(
            BitvectorExpression.create(jA, BitvectorOperator.XOR, jB), BitvectorOperator.XOR, jX);

    Expr assignment1 = em.mkExpr(Kind.EQUAL, new_x_, a_xor_b_xor_x);
    NumericBooleanExpression jAssignment1 = NumericBooleanExpression.create(jNewX_, EQ, jAxorBxorX);

    // Assert encoding to CVC4 in current context;
    smt.assertFormula(assignment1);
    cvc4Context.add(jAssignment1);

    Expr new_x_eq_new_x_ = em.mkExpr(Kind.EQUAL, new_x, new_x_);
    NumericBooleanExpression jNewXEqNewX_ = NumericBooleanExpression.create(jNewX, EQ, jNewX_);

    Result res = smt.checkSat();
    ConstraintSolver.Result jRes = cvc4Context.isSatisfiable();

    assertEquals(jRes, CVC4Solver.convertCVC4Res(res));

    smt.pop();
    cvc4Context.pop();
    // Encoding code (2)
    // new_x_ = a + b - x
    Expr a_plus_b = em.mkExpr(Kind.BITVECTOR_PLUS, a, b);
    NumericCompound aPlusB = NumericCompound.create(jA, PLUS, jB);

    Expr a_plus_b_minus_x = em.mkExpr(Kind.BITVECTOR_SUB, a_plus_b, x);
    NumericCompound aPlusBminusX = NumericCompound.create(aPlusB, PLUS, jX);

    Expr assignment2 = em.mkExpr(Kind.EQUAL, new_x_, a_plus_b_minus_x);
    NumericBooleanExpression jAssignment2 =
        NumericBooleanExpression.create(jNewX_, EQ, aPlusBminusX);

    // Assert encoding to CVC4 in current context;
    smt.assertFormula(assignment2);
    cvc4Context.add(jAssignment2);

    Result res2 = smt.checkSat();
    ConstraintSolver.Result jRes2 = cvc4Context.isSatisfiable();

    assertEquals(jRes2, CVC4Solver.convertCVC4Res(res2));
  }

  // TODO: jConstraints does not support the Array Theorie yet. Fix this first.
  @Test(enabled = false)
  public void evaluatesExpression() {
    smt.setLogic("QF_AUFBV");

    // Consider the following code (where size is some previously defined constant):
    //
    //   Assert (current_array[0] > 0);
    //   for (unsigned i = 1; i < k; ++i) {
    //     current_array[i] = 2 * current_array[i - 1];
    //     Assert (current_array[i-1] < current_array[i]);
    //   }
    //
    // We want to check whether the assertion in the body of the for loop holds
    // throughout the loop.

    // Setting up the problem parameters
    int k = 4; // number of unrollings (should be a power of 2)
    int index_size = log2(k); // size of the index

    // Types
    Type elementType = em.mkBitVectorType(32);
    Type indexType = em.mkBitVectorType(index_size);
    Type arrayType = em.mkArrayType(indexType, elementType);

    // Variables
    Expr current_array = em.mkVar("current_array", arrayType);

    // Making a bit-vector constant
    Expr zero = em.mkConst(new BitVector(index_size, 0));

    // Asserting that current_array[0] > 0
    Expr current_array0 = em.mkExpr(Kind.SELECT, current_array, zero);
    Expr current_array0_gt_0 =
        em.mkExpr(Kind.BITVECTOR_SGT, current_array0, em.mkConst(new BitVector(32, 0)));
    smt.assertFormula(current_array0_gt_0);

    // Building the assertions in the loop unrolling
    Expr index = em.mkConst(new BitVector(index_size, 0));
    Expr old_current = em.mkExpr(Kind.SELECT, current_array, index);
    Expr two = em.mkConst(new BitVector(32, 2));

    vectorExpr assertions = new vectorExpr(em);
    for (int i = 1; i < k; ++i) {
      index = em.mkConst(new BitVector(index_size, new edu.stanford.CVC4.Integer(i)));
      Expr new_current = em.mkExpr(Kind.BITVECTOR_MULT, two, old_current);
      // current[i] = 2 * current[i-1]
      current_array = em.mkExpr(Kind.STORE, current_array, index, new_current);
      // current[i-1] < current [i]
      Expr current_slt_new_current = em.mkExpr(Kind.BITVECTOR_SLT, old_current, new_current);
      assertions.add(current_slt_new_current);

      old_current = em.mkExpr(Kind.SELECT, current_array, index);
    }

    Expr query = em.mkExpr(Kind.NOT, em.mkExpr(Kind.AND, assertions));
    smt.assertFormula(query);

    Result.Sat expect = Result.Sat.SAT;
    Result.Sat actual = smt.checkSat(em.mkConst(true)).isSat();
    assertEquals(expect, actual);
  }

  private static int log2(int n) {
    return (int) Math.round(Math.log(n) / Math.log(2));
  }

  @Test
  public void combinationTest() {
    smt.setLogic("QF_UFLIRA");

    // Sorts
    SortType u = em.mkSort("u");
    NamedSort jU = new NamedSort("u");

    Type integer = em.integerType();
    Type booleanType = em.booleanType();
    Type uToInt = em.mkFunctionType(u, integer);
    Type intPred = em.mkFunctionType(integer, booleanType);

    // Variables
    Expr x = em.mkVar("x", u);
    Variable jX = Variable.create(jU, "X");
    Expr y = em.mkVar("y", u);
    Variable jY = Variable.create(jU, "Y");

    // Functions
    Expr f = em.mkVar("f", uToInt);
    Function jF = new Function("f", BuiltinTypes.INTEGER, jU);
    Expr p = em.mkVar("p", intPred);
    Function jP = new Function("p", BuiltinTypes.BOOL, BuiltinTypes.INTEGER);

    // Constants
    Expr zero = em.mkConst(new Rational(0));
    Constant jZero = Constant.create(BuiltinTypes.REAL, BigFraction.ZERO);
    Expr one = em.mkConst(new Rational(1));
    Constant jOne = Constant.create(BuiltinTypes.REAL, BigFraction.ONE);

    // Terms
    Expr f_x = em.mkExpr(Kind.APPLY_UF, f, x);
    FunctionExpression jFx = new FunctionExpression(jF, jX);

    Expr f_y = em.mkExpr(Kind.APPLY_UF, f, y);
    FunctionExpression jFy = new FunctionExpression(jF, jY);

    Expr sum = em.mkExpr(Kind.PLUS, f_x, f_y);
    NumericCompound jSum = NumericCompound.create(jFx, PLUS, jFy);

    Expr p_0 = em.mkExpr(Kind.APPLY_UF, p, zero);
    FunctionExpression jP0 = new FunctionExpression(jP, jZero);

    Expr p_f_y = em.mkExpr(Kind.APPLY_UF, p, f_y);
    FunctionExpression jPfy = new FunctionExpression(jP, jFy);

    // Construct the assumptions
    Expr assumptions =
        em.mkExpr(
            Kind.AND,
            em.mkExpr(Kind.LEQ, zero, f_x), // 0 <= f(x)
            em.mkExpr(Kind.LEQ, zero, f_y), // 0 <= f(y)
            em.mkExpr(Kind.LEQ, sum, one), // f(x) + f(y) <= 1
            p_0.notExpr(), // not p(0)
            p_f_y); // p(f(y))

    NumericBooleanExpression part1 = NumericBooleanExpression.create(jZero, LE, jFx);
    NumericBooleanExpression part2 = NumericBooleanExpression.create(jZero, LE, jFy);
    NumericBooleanExpression part3 = NumericBooleanExpression.create(jSum, LE, jOne);
    Negation notP0 = Negation.create(jP0);

    PropositionalCompound assumption = PropositionalCompound.create(part1, AND, part2);
    assumption = PropositionalCompound.create(assumption, AND, part3);
    assumption = PropositionalCompound.create(assumption, AND, notP0);
    assumption = PropositionalCompound.create(assumption, AND, jPfy);

    cvc4Context.add(assumption);

    cvc4Context.push();

    NumericBooleanExpression distinct = NumericBooleanExpression.create(jX, NE, jY);
    cvc4Context.add(distinct);
    assertEquals(ConstraintSolver.Result.SAT, cvc4Context.isSatisfiable());

    cvc4Context.pop();
    assertEquals(ConstraintSolver.Result.SAT, cvc4Context.isSatisfiable());
  }
}
