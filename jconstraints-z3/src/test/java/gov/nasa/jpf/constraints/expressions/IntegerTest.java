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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.Properties;
import org.testng.annotations.AfterClass;
import org.testng.annotations.AfterMethod;
import org.testng.annotations.BeforeClass;
import org.testng.annotations.BeforeMethod;
import org.testng.annotations.Test;

public class IntegerTest {

  public IntegerTest() {}

  @Test
  public void testIntegerFunction() {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    ConstraintSolver solver = factory.createSolver("z3");
    SolverContext ctx = solver.createContext();

    Variable x = new Variable(BuiltinTypes.SINT32, "x");
    Variable y = new Variable(BuiltinTypes.SINT32, "y");
    // Expression expr = new NumericBooleanExpression(x, NumericComparator.EQ, x);

    Expression expr =
        new NumericBooleanExpression(
            y, NumericComparator.EQ, new FunctionExpression<>(MathFunctions.IABS, x));

    ctx.add(expr);

    Valuation val = new Valuation();
    Result r = ctx.solve(val);
    System.out.println(r + ": " + val);
  }

  @BeforeClass
  public static void setUpClass() throws Exception {}

  @AfterClass
  public static void tearDownClass() throws Exception {}

  @BeforeMethod
  public void setUpMethod() throws Exception {}

  @AfterMethod
  public void tearDownMethod() throws Exception {}
}
