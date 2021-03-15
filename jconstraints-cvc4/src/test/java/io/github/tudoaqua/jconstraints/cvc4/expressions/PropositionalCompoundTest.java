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

package io.github.tudoaqua.jconstraints.cvc4.expressions;

import static org.testng.Assert.assertEquals;
import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import io.github.tudoaqua.jconstraints.cvc4.AbstractCVC4Test;
import org.testng.annotations.Test;

public class PropositionalCompoundTest extends AbstractCVC4Test {

  @Test
  public void propositionalCompoundEquivTest() {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");
    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    Valuation val = new Valuation();
    Result res = cvc4.solve(pc, val);
    assertEquals(res, Result.SAT);
    assertTrue(pc.evaluate(val));
  }
}
