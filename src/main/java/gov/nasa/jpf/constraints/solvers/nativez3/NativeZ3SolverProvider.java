/*
 * Copyright (C) 2015, United States Government, as represented by the 
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment 
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you 
 * may not use this file except in compliance with the License. You may obtain a 
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software distributed 
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR 
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the 
 * specific language governing permissions and limitations under the License.
 */
package gov.nasa.jpf.constraints.solvers.nativez3;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.util.HashMap;
import java.util.Map;

import java.util.Properties;

public class NativeZ3SolverProvider implements ConstraintSolverProvider {

  @Override
  public String[] getNames() {
    return new String[]{"z3", "Z3"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    Map<String, String> options = new HashMap<>();
    int timeout = -1;

    if (config.containsKey("z3.options")) {
      String conf = config.getProperty("z3.options").trim();
      String[] opts = conf.split(";");
      for (String o : opts) {
        o = o.trim();
        if (o.length() < 1) {
          continue;
        }

        String[] kv = o.split("=");
        if (kv.length != 2) {
          System.err.println("Warning: " + o + " is not a valid option to z3.");
          continue;
        }
        options.put(kv[0].trim(), kv[1].trim());
      }
    }

    if (config.containsKey("z3.timeout")) {
      timeout = Integer.parseInt(config.getProperty("z3.timeout"));
    }

    return new NativeZ3Solver(timeout, options);
  }

}
