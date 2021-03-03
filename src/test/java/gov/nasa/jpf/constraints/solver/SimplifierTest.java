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

/** @author falk */
public class SimplifierTest {

  @Test
  public void eliminationTest() throws IOException {
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    NativeZ3Solver solver = (NativeZ3Solver) factory.createSolver("Z3", conf);

    Variable a = new Variable(BuiltinTypes.INTEGER, "a");

    Constant zero = new Constant(BuiltinTypes.INTEGER, BigInteger.ZERO);
    Constant two = new Constant(BuiltinTypes.INTEGER, BigInteger.valueOf(2));

    Expression<Boolean> expr =
        ExpressionUtil.and(
            new NumericBooleanExpression(a, NumericComparator.GT, zero),
            new NumericBooleanExpression(a, NumericComparator.EQ, two));

    System.out.println("IN: " + expr);
    Expression<Boolean> expr2 = solver.simplify(expr);
    System.out.println("SIMPLIFIED: " + expr2);
    assertNotNull(expr2);
  }
}
