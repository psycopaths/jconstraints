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

package gov.nasa.jpf.constraints.solvers;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolverProvider;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.Set;

public class SolvingService extends ConstraintSolver {
  ArrayList<String> supportedSolvers;
  Set<ConstraintSolver> solvers;

  private Set<String> toBeIngored;

  public SolvingService() {
    supportedSolvers = new ArrayList();
    solvers = new HashSet<>();
    toBeIngored = new HashSet<>();
    toBeIngored.add(DontKnowSolverProvider.providerName);

    init(null);
  }

  public SolvingService(Properties config) {
    this();

    List<String> allowed = parseAllowedSolvers(config.getProperty("solving.allowedSolver", null));
    init(allowed);
  }

  public SolvingService(Set<ConstraintSolver> solvers) {
    this();
    this.solvers = solvers;
    supportedSolvers.clear();
    for (ConstraintSolver solver : solvers) {
      supportedSolvers.add(solver.getName());
    }
  }

  private List<String> parseAllowedSolvers(String input) {
    List<String> result = new ArrayList<>();
    if (input != null) {
      for (String solver : input.split(",")) {
        result.add(solver);
      }
    }
    return result;
  }

  private void init(List<String> allowed) {
    Set<String> availableProviderNames = ConstraintSolverFactory.getLoadedProviders();

    Set<Class> solverClasses = new HashSet<>();
    for (String name : availableProviderNames) {
      if (allowed != null && !allowed.contains(name) || toBeIngored.contains(name)) {
        continue;
      }
      supportedSolvers.add(name);
      ConstraintSolver solver = ConstraintSolverFactory.getRootFactory().createSolver(name);
      if (!solverClasses.contains(solver.getClass())) {
        solvers.add(solver);
        solverClasses.add(solver.getClass());
      }
    }
  }

  public Result solveAll(Expression expr, Valuation res) {
    HashSet<Result> result = new HashSet<>();
    for (ConstraintSolver solver : solvers) {
      try {
        Result tmp = solver.solve(expr, res);
        if (result.isEmpty()) {
          result.add(tmp);
        } else if (!result.contains(tmp)) {
          throw new RuntimeException("Result mismatch! Expected " + result + " , but got: " + tmp);
        }
      } catch (UnsupportedOperationException e) {
        // This might happen sometimes
      }
    }
    return result.iterator().next();
  }

  public Result solve(SMTProblem problem) {
    HashSet<Result> result = new HashSet<>();
    for (ConstraintSolver solver : solvers) {
      try {
        SolverContext ctx = solver.createContext();
        ctx.add(problem.assertions);
        Result tmp = ctx.solve(null);
        if (!result.contains(tmp) && !result.isEmpty()) {
          throw new RuntimeException("Result mismatch! Expected " + result + " , but got: " + tmp);
        }
        result.add(tmp);
      } catch (UnsupportedOperationException e) {
        // Some solver don't support a context, so we just don't support them.
      }
    }
    return result.iterator().next();
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    return solveAll(f, result);
  }
}
