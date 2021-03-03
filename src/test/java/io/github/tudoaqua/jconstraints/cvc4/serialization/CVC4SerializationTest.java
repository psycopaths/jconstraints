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
package io.github.tudoaqua.jconstraints.cvc4.serialization;

import static org.testng.Assert.assertEquals;
import static org.testng.AssertJUnit.assertTrue;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import io.github.tudoaqua.jconstraints.cvc4.CVC4Solver;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.util.HashMap;
import org.testng.annotations.Test;

public class CVC4SerializationTest {

  @Test(enabled = false, expectedExceptions = EvaluationException.class)
  public void exprUnsatTest() throws IOException, ClassNotFoundException {
    InputStream is = new FileInputStream("/tmp/serialized_cvc4200145360267212");
    ObjectInputStream ois = new ObjectInputStream(is);
    Expression f = (Expression) ois.readObject();

    CVC4Solver cvc4 = new CVC4Solver(new HashMap<>());
    Valuation val = new Valuation();
    Result res = cvc4.solve(f, val);
    assertEquals(res, Result.UNSAT);
    f.evaluate(val);
  }

  @Test(enabled = false)
  public void exprSatTest() throws IOException, ClassNotFoundException {
    InputStream is = new FileInputStream("/tmp/serialized_cvc4998978124819");
    ObjectInputStream ois = new ObjectInputStream(is);
    Expression f = (Expression) ois.readObject();

    CVC4Solver cvc4 = new CVC4Solver(new HashMap<>());
    Valuation val = new Valuation();
    Result res = cvc4.solve(f, val);
    assertEquals(res, Result.SAT);
    assertTrue((Boolean) f.evaluate(val));
  }
}
