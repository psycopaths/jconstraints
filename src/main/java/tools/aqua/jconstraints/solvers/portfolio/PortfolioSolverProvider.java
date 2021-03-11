/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>The JConstraints Meta-Solver is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tools.aqua.jconstraints.solvers.portfolio;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.util.Properties;

public class PortfolioSolverProvider implements
    ConstraintSolverProvider {

  @Override
  public String[] getNames() {
    return new String[]{"portfolio", "Portfolio", "parallel", "multi"};
  }

  @Override
  public ConstraintSolver createSolver(Properties properties) {
    return new PortfolioSolver(properties);
  }
}
