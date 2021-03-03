/*
 * Copyright 2017-2021 The jConstraints-cvc4 Authors
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

/**
 * Copyright 2020 TU Dortmund, Nils Schmidt und Malte Mues
 *
 * <p>Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 *
 * <p>http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
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
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import java.util.HashMap;
import org.testng.annotations.Test;

public class PropositionalCompoundTest {

  @Test
  public void propositionalCompoundEquivTest() {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");
    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    CVC4Solver cvc4 = new CVC4Solver(new HashMap<>());
    Valuation val = new Valuation();
    Result res = cvc4.solve(pc, val);
    assertEquals(res, Result.SAT);
    assertTrue(pc.evaluate(val));
  }
}
