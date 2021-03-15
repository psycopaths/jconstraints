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
package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class CVC4SolverProvider implements ConstraintSolverProvider {

  @Override
  public String[] getNames() {
    return new String[] {"cvc4", "CVC4"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    Map<String, String> options = new HashMap<>();
    if (!config.containsKey("cvc4.options")) {
      // TODO Throw Something
    } else {
      String conf = config.getProperty("cvc4.options").trim();
      String[] opts = conf.split(";");
      for (String o : opts) {
        o = o.trim();
        if (o.length() >= 1) {
          String[] val = o.split("=");
          options.put(val[0].trim(), val[1].trim());
        }
      }
    }
    return new CVC4Solver(options);
  }
}
