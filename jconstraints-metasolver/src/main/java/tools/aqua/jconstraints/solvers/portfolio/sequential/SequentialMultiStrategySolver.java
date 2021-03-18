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

/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>The JConstraints Meta-Solver is licensed under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tools.aqua.jconstraints.solvers.portfolio.sequential;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

public class SequentialMultiStrategySolver extends ConstraintSolver {

  // Internal solverNames
  static final String CVC4 = "cvc4process";
  static final String Z3 = "z3";

  private final Map<String, ConstraintSolver> solvers;
  private boolean isCVC4enabled = true;

  public SequentialMultiStrategySolver(Properties properties) {
    solvers = new HashMap<>();
    setupSolvers(properties);
  }

  @Override
  public Result solve(Expression<Boolean> expression, Valuation valuation) {
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = expression.accept(visitor, null);
    if (isCVC4enabled && isStringOrFloatExpression) {
      Result res = solvers.get(CVC4).solve(expression, valuation);
      if (res.equals(Result.SAT)) {
        try {
          boolean evaluation = expression.evaluateSMT(valuation);
          if (!evaluation) {
            res = Result.DONT_KNOW;
          }
        } catch (Exception e) {
          res = Result.DONT_KNOW;
        }
      }
      if (!res.equals(Result.DONT_KNOW)) {
        return res;
      } else {
        isCVC4enabled = false;
        System.out.println("Disable process solver and shutdown exec");
        return solve(expression, valuation);
      }
    } else {
      return solvers.get(Z3).solve(expression, valuation);
    }
  }

  @Override
  public SolverContext createContext() {
    Map<String, SolverContext> ctxs = new HashMap<>();
    for (Entry<String, ConstraintSolver> s : solvers.entrySet()) {
      ctxs.put(s.getKey(), s.getValue().createContext());
    }
    return new SequentialMultiStrategySolverContext(ctxs);
  }

  private void setupSolvers(Properties properties) {
    ConstraintSolverFactory csf = new ConstraintSolverFactory();
    solvers.put(CVC4, csf.createSolver(CVC4, properties));
    solvers.put(Z3, csf.createSolver(Z3, properties));
  }
}
