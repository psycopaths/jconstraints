/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * <p>Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com) We
 * license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.expressions;

import static org.testng.AssertJUnit.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.AsinProperties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.Atan2Properties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.CosProperties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.PowProperties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.SinProperties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.SqrtProperties;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3SolverContext;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Properties;
import org.testng.annotations.Test;

@Test
public class TrigonometricTest {

  private SolverContext createContext(Properties conf) {
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.mbqi=true;smt.macro-finder=true");
    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
    ConstraintSolver solver = factory.createSolver();
    SolverContext ctx = solver.createContext();
    return ctx;
  }

  @Test
  public void testAtan2() {
    Properties conf = new Properties();
    conf.setProperty("z3.timeout", "1");
    SolverContext ctx = createContext(conf);

    SqrtProperties sqrt = new SqrtProperties(15);
    Atan2Properties atan2 = new Atan2Properties(15, sqrt);

    ctx.add(sqrt.getDefinition());
    ctx.add(atan2.getDefinition());

    Variable<Double> x = new Variable<>(BuiltinTypes.DOUBLE, "x");
    Variable<Double> y = new Variable<>(BuiltinTypes.DOUBLE, "y");

    ctx.add(
        new NumericBooleanExpression(
            new Constant<>(BuiltinTypes.DOUBLE, 0.0), NumericComparator.LT, x));

    ctx.add(
        new NumericBooleanExpression(
            new Constant<>(BuiltinTypes.DOUBLE, 0.0),
            NumericComparator.LT,
            new FunctionExpression<>(MathFunctions.ATAN2, y, x)));

    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    System.out.println(res + " : " + val);
    assertEquals(Result.DONT_KNOW, res);
  }

  // FIXME: This takes very long with Floating Points
  @Test(enabled = false)
  public void testTrigonometrics() {

    Properties conf = new Properties();
    // conf.setProperty("z3.timeout", "1000");
    SolverContext ctx = createContext(conf);

    AsinProperties asin = new AsinProperties(10);
    SinProperties sin = new SinProperties(10);
    CosProperties cos = new CosProperties(sin);

    ctx.add(asin.getDefinition());
    ctx.add(sin.getDefinition());
    ctx.add(cos.getDefinition());

    // ctx.add(asin.getRangeBounds());
    // ctx.add(cos.getRangeBounds());

    Variable<Double> head = new Variable<>(BuiltinTypes.DOUBLE, "head");

    // (assert (<= (* 57.29577951308232 (_asin (+ 0.6130455374565814
    // (* 0.01204238407208075 (_cos (+ 3.141592653589793
    // (* head 0.017453292519943295)) ) )  ))) 90.0))

    NumericCompound<Double> cosArg =
        new NumericCompound<>(
            new Constant<>(BuiltinTypes.DOUBLE, 3.141592653589793),
            NumericOperator.PLUS,
            new NumericCompound<>(
                new Constant<>(BuiltinTypes.DOUBLE, 0.017453292519943295),
                NumericOperator.MUL,
                head));

    NumericCompound<Double> asinArg =
        new NumericCompound<>(
            new Constant<>(BuiltinTypes.DOUBLE, 0.6130455374565814),
            NumericOperator.PLUS,
            new NumericCompound<>(
                new Constant<>(BuiltinTypes.DOUBLE, 0.01204238407208075),
                NumericOperator.MUL,
                new FunctionExpression<>(MathFunctions.COS, cosArg)));

    Expression<Boolean> test =
        new NumericBooleanExpression(
            new Constant<>(BuiltinTypes.DOUBLE, 90.0),
            NumericComparator.GE,
            new NumericCompound<>(
                new Constant<>(BuiltinTypes.DOUBLE, 57.29577951308232),
                NumericOperator.MUL,
                new FunctionExpression<>(MathFunctions.ASIN, asinArg)));

    ctx.add(cos.getDomainBounds(cosArg));
    ctx.add(asin.getDomainBounds(asinArg));
    ctx.add(test);

    Valuation val = new Valuation();
    Result res = ctx.solve(val);
    System.out.println(res + " : " + val);
    assertEquals(Result.SAT, res);
    System.out.println(test.evaluate(val));
  }

  // FIXME: Running on real FP this takes realy long for a unit test.
  @Test(enabled = false)
  public void testCoral1() {
    // Constraint: (sin(x1) - cos(x2)) = 0.0
    //        && x1 >= -1
    //        && x2 <= 1
    Properties conf = new Properties();
    // conf.setProperty("z3.timeout", "1000");
    SolverContext ctx = createContext(conf);

    SinProperties sin = new SinProperties(10);
    CosProperties cos = new CosProperties(sin);

    ctx.add(sin.getDefinition());
    ctx.add(cos.getDefinition());

    Variable x1 = new Variable(BuiltinTypes.DOUBLE, "x1");
    Variable x2 = new Variable(BuiltinTypes.DOUBLE, "x2");

    // ctx.add(sin.getRangeBounds());
    // ctx.add(cos.getRangeBounds());

    ctx.add(sin.getDomainBounds(x1));
    ctx.add(cos.getDomainBounds(x2));

    Expression<Boolean> test =
        new NumericBooleanExpression(
            new NumericCompound(
                new FunctionExpression(MathFunctions.SIN, x1),
                NumericOperator.MINUS,
                new FunctionExpression<>(MathFunctions.COS, x2)),
            NumericComparator.EQ,
            new Constant<>(BuiltinTypes.DOUBLE, 0.0));

    ctx.add(test);

    Valuation val = new Valuation();
    assert (ctx instanceof NativeZ3SolverContext);
    Result res = ((NativeZ3SolverContext) ctx).approximate(val);
    System.out.println(res + " : " + val);
    System.out.println(test.evaluate(val));
    System.out.println("sin(x1): " + Math.sin((Double) val.getValue(x1)));
    System.out.println("cos(x2): " + Math.cos((Double) val.getValue(x2)));
    System.out.println(Math.sin((Double) val.getValue(x1)) - Math.cos((Double) val.getValue(x2)));
    assertEquals(Result.SAT, res);
  }

  // FIXME: Running on real FP this takes realy long for a unit test.
  @Test(enabled = false)
  public void testCoral2() {
    // Constraint: (sin(x1) - cos(x2)) = 0.0
    //        && x1 >= -1
    //        && x2 <= 1
    Properties conf = new Properties();
    // conf.setProperty("z3.timeout", "1000");
    SolverContext ctx = createContext(conf);

    PowProperties pow = new PowProperties();
    SinProperties sin = new SinProperties(10);
    CosProperties cos = new CosProperties(sin);

    ctx.add(pow.getDefinition());
    ctx.add(sin.getDefinition());
    ctx.add(cos.getDefinition());

    // && c1 == 0.017453292519943295
    Constant c1 = new Constant(BuiltinTypes.DOUBLE, 0.017453292519943295);
    Constant zero = new Constant(BuiltinTypes.DOUBLE, 0.0);
    Variable x1 = new Variable(BuiltinTypes.DOUBLE, "x1");
    Variable x2 = new Variable(BuiltinTypes.DOUBLE, "x2");
    Variable x3 = new Variable(BuiltinTypes.DOUBLE, "x3");
    Variable x4 = new Variable(BuiltinTypes.DOUBLE, "x4");
    Variable x5 = new Variable(BuiltinTypes.DOUBLE, "x5");

    // && x5 != 0.0
    ctx.add(new NumericBooleanExpression(x5, NumericComparator.NE, zero));

    // a1: pow(((x1 * sin(((c1 * x2) - (c1 * x3)))) - (0.0 * x4)), 2.0)
    FunctionExpression pow1 =
        new FunctionExpression(
            MathFunctions.POW,
            new NumericCompound(
                new NumericCompound(
                    x1,
                    NumericOperator.MUL,
                    new FunctionExpression<>(
                        MathFunctions.SIN,
                        new NumericCompound(
                            new NumericCompound(c1, NumericOperator.MUL, x2),
                            NumericOperator.MINUS,
                            new NumericCompound(c1, NumericOperator.MUL, x3)))),
                NumericOperator.MINUS,
                new NumericCompound(zero, NumericOperator.MUL, x4)),
            new Constant<>(BuiltinTypes.DOUBLE, 2.0));

    // + pow((x1 * cos((((c1 * x2) - (c1 * x3)) + 0.0))), 2.0)
    FunctionExpression pow2 =
        new FunctionExpression(
            MathFunctions.POW,
            new NumericCompound(
                x1,
                NumericOperator.MUL,
                new FunctionExpression<>(
                    MathFunctions.COS,
                    new NumericCompound(
                        new NumericCompound(
                            new NumericCompound(c1, NumericOperator.MUL, x2),
                            NumericOperator.MINUS,
                            new NumericCompound(c1, NumericOperator.MUL, x3)),
                        NumericOperator.PLUS,
                        zero))),
            new Constant<>(BuiltinTypes.DOUBLE, 2.0));

    // Constraint: 0.0 == a1
    NumericCompound a1 = new NumericCompound(pow1, NumericOperator.PLUS, pow2);
    Expression<Boolean> test = new NumericBooleanExpression(zero, NumericComparator.EQ, a1);

    ctx.add(test);

    Valuation val = new Valuation();
    assert (ctx instanceof NativeZ3SolverContext);
    Result res = ((NativeZ3SolverContext) ctx).approximate(val);
    System.out.println(res + " : " + val);
    System.out.println(test.evaluate(val));
    assertEquals(Result.SAT, res);
  }

  // Constraint: sqrt(pow(((x1 + (e1 * (cos(x4) - cos((x4 + (((1.0 * (((c1 * x5) * (e2/c2))/x6))
  // * x2)/e1)))))) -
  //        (((e2/c2)) * (1.0 - cos((c1 * x5))))), 2.0)) > 999.0
  //        && (c1 * x5) > 0.0
  //        && x3 > 0.0
  //        && x6 > 0.0
  //        && c1 = 0.017453292519943295
  //        && c2 = 68443.0
  //        && e1 = ((pow(x2, 2.0) / tan((c1 * x3)))/c2)
  //        && e2 = pow(x6, 2.0) / tan((c1 * x3))

}
