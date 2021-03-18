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

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperContext;
import java.util.List;
import java.util.Map;

public class SequentialMultiStrategySolverContext extends SolverContext {

  private Map<String, SolverContext> solvers;
  private boolean isCVC4Enabled = true;
  private boolean isZ3CtxBroken = true;

  public SequentialMultiStrategySolverContext(Map<String, SolverContext> ctxs) {
    this.solvers = ctxs;
  }

  @Override
  public void push() {
    for (SolverContext ctx : solvers.values()) {
      ctx.push();
    }
  }

  @Override
  public void pop(int i) {
    for (SolverContext ctx : solvers.values()) {
      ctx.pop(i);
    }
  }

  @Override
  public Result solve(Valuation valuation) {
    ProcessWrapperContext ctx =
        (ProcessWrapperContext) solvers.get(SequentialMultiStrategySolver.CVC4);
    Expression expression = ctx.getCurrentExpression();
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = (Boolean) expression.accept(visitor, null);
    Result res;
    if (isCVC4Enabled && isStringOrFloatExpression) {
      res = solvers.get(SequentialMultiStrategySolver.CVC4).solve(valuation);

      if (res.equals(Result.DONT_KNOW) && !isZ3CtxBroken) {
        System.out.println("Disable process solver and shutdown exec");
        isCVC4Enabled = false;
        return solve(valuation);
      }
    } else {
      res = solvers.get(SequentialMultiStrategySolver.Z3).solve(valuation);
    }

    if (res.equals(Result.DONT_KNOW)) {
      return res;
    }
    if (res.equals(Result.SAT)) {
      try {
        assert (Boolean) expression.evaluateSMT(valuation);
      } catch (Exception e) {
        res = Result.DONT_KNOW;
      }
    }
    return res;
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    try {
      for (SolverContext ctx : solvers.values()) {
        ctx.add(list);
      }
    } catch (RuntimeException e) {
      isZ3CtxBroken = true;
    }
  }

  @Override
  public void dispose() {
    for (SolverContext ctx : solvers.values()) {
      ctx.dispose();
    }
  }
}
