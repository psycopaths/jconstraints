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

import java.util.Properties;
import java.util.logging.Logger;

@Deprecated
public class NativeZ3SolverProviderLegacy extends NativeZ3SolverProvider {

  private static final Logger logger = Logger.getLogger("constraints");

  @Override
  public String[] getNames() {
    return new String[]{"NativeZ3"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    logger.warning("Using deprecated solver name 'NativeZ3' might fail in future releases");
    return super.createSolver(config);
  }
}
