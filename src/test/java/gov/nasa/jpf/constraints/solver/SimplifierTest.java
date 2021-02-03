/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package gov.nasa.jpf.constraints.solver;

import static org.testng.Assert.assertNotNull;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.math.BigInteger;
import java.util.Properties;
import org.testng.annotations.Test;

/**
 *
 * @author falk
 */
public class SimplifierTest {
    
  @Test
  public void eliminationTest() throws IOException {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
    NativeZ3Solver solver = (NativeZ3Solver) factory.createSolver();

    Variable a = new Variable(BuiltinTypes.INTEGER, "a");

    Constant zero = new Constant(BuiltinTypes.INTEGER, BigInteger.ZERO);
    Constant two = new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(2));

    Expression<Boolean> expr = ExpressionUtil.and(
        new NumericBooleanExpression(a, NumericComparator.GT, zero),
        new NumericBooleanExpression(a, NumericComparator.EQ, two));

    System.out.println("IN: " + expr);
    Expression<Boolean> expr2 = solver.simplify(expr);
    System.out.println("SIMPLIFIED: " + expr2);
    assertNotNull(expr2);
  }    
}
