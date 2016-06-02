/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.solver;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import org.junit.Before;
import static org.junit.Assert.*;
import org.testng.annotations.Test;

/**
 *
 * @author mmuesly
 */
public class QuantifierEliminationTest {
  
  public QuantifierEliminationTest() {
  }
  
  @Before
  public void setUp() {
  }

  @Test
  public void eliminationTest() throws IOException {
    Properties conf = new Properties();     
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
    NativeZ3Solver solver = (NativeZ3Solver)factory.createSolver();        

    Variable x = new Variable(BuiltinTypes.INTEGER, "x");
    Variable a = new Variable(BuiltinTypes.INTEGER, "a");
    Variable b = new Variable(BuiltinTypes.INTEGER, "b");

    Constant zero = new Constant(BuiltinTypes.INTEGER, 0);

    //Expression expr = new NumericBooleanExpression(x, NumericComparator.EQ, x);

    Expression expr = new NumericBooleanExpression(
            x, 
            NumericComparator.EQ,
            new NumericCompound<>(a, NumericOperator.PLUS, b));                

    expr = ExpressionUtil.and(expr,
            new NumericBooleanExpression(a, NumericComparator.GT, zero),
            new NumericBooleanExpression(b, NumericComparator.GT, zero));

    List bound = new ArrayList<>();
    bound.add(a);
    bound.add(b);

    QuantifierExpression qe = new QuantifierExpression(Quantifier.EXISTS, bound, expr);
    System.out.println("gov.nasa.jpf.constraints.api.QuantifierEliminationTest.eliminationTest()");
    StringBuilder aa = new StringBuilder();
    qe.print(aa);
    System.out.println(aa.toString());
    assertNotNull(solver.eliminateQuantifiers(qe));
  }
}
