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

import static gov.nasa.jpf.constraints.expressions.NumericComparator.EQ;
import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.SkipException;
import org.testng.annotations.Test;

public class CVC4SolverProviderTest {

  /* We disabled this as the memory clean up during Garbage collection in CVC4 is error prune.
    In applications and other enabled tests, we rap CVC4 in its own process. Once there is a new
    Java API JNI-Library, stabilizing these tests by making the JNI-Library robust against garbage collection.
    https://github.com/CVC4/CVC4/issues/5018
  */
  @Test(enabled = false)
  public void cvc4ServiceLoaderTest() {
    CVC4Solver solver;
    try {
      solver = (CVC4Solver) ConstraintSolverFactory.createSolver("cvc4");
    } catch (UnsatisfiedLinkError e) {
      throw new SkipException("No native CVC4 support", e);
    }
    Valuation val = new Valuation();
    Variable x = Variable.create(BuiltinTypes.SINT32, "X");
    Constant c5 = Constant.create(BuiltinTypes.SINT32, 5);
    NumericBooleanExpression nbe = NumericBooleanExpression.create(x, EQ, c5);
    Result res = solver.solve(nbe, val);
    assertEquals(res, Result.SAT);
    assertTrue(nbe.evaluate(val));
  }
}
