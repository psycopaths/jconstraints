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

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperContext;
import gov.nasa.jpf.constraints.solvers.encapsulation.SolvingResult;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class PortfolioSolverContext extends SolverContext {

  private List<ProcessWrapperContext> solvers;
  private List<SolverContext> direct;
  private ExecutorService exec;
  private boolean isProcessSolverDisabled;
  private boolean isDirectBroken;

  public PortfolioSolverContext(List<ProcessWrapperContext> ctxs, List<SolverContext> direct) {
    this.solvers = ctxs;
    this.direct = direct;
    this.exec = null;
    this.isProcessSolverDisabled = false;
    this.isDirectBroken = false;
  }

  @Override
  public void push() {
    for (SolverContext ctx : solvers) {
      ctx.push();
    }
    for (SolverContext ctx : direct) {
      ctx.push();
    }
  }

  @Override
  public void pop(int i) {
    for (SolverContext ctx : solvers) {
      ctx.pop(i);
    }
    for (SolverContext ctx : direct) {
      ctx.pop(i);
    }
  }

  @Override
  public Result solve(Valuation valuation) {
    ProcessWrapperContext ctx = solvers.get(0);
    Expression expression = ctx.getCurrentExpression();
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = (Boolean) expression.accept(visitor, null);
    if (!isProcessSolverDisabled && isStringOrFloatExpression) {
      exec = Executors.newFixedThreadPool(solvers.size());
      List<SolverContext> wrappedCtxs = new LinkedList<>();
      for (ProcessWrapperContext solver : solvers) {
        if (solver.getName().equalsIgnoreCase("cvc4")) {
          wrappedCtxs.add(solver);
        }
      }
      Result res = dispatcheProcessWrappedSolvers(expression, valuation, wrappedCtxs);
      if (res.equals(Result.DONT_KNOW) && !isDirectBroken) {
        isProcessSolverDisabled = true;
        System.out.println("Disable process solver and shutdown exec");
        exec.shutdown();
        exec = null;
        return solve(valuation);
      } else {
        return res;
      }
    } else {
      if (direct.size() == 1) {
        return direct.get(0).solve(valuation);
      }
    }
    throw new IllegalArgumentException("Cannot run the problem with the provided solvers");
  }

  public Result dispatcheProcessWrappedSolvers(
      Expression<Boolean> expression, Valuation valuation, List<SolverContext> solvers) {
    List<Runnable> calls = new LinkedList<>();
    ExecutorCompletionService ecs = new ExecutorCompletionService(exec);
    for (SolverContext solver : solvers) {
      ecs.submit(
          () -> {
            Valuation val = new Valuation();
            Result res = solver.solve(val);
            return new SolvingResult(res, val);
          });
    }
    return PortfolioSolver.processResult(solvers.size(), ecs, valuation);
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    for (SolverContext ctx : solvers) {
      ctx.add(list);
    }
    try {
      for (SolverContext ctx : direct) {
        ctx.add(list);
      }
    } catch (RuntimeException e) {
      isDirectBroken = true;
    }
  }

  @Override
  public void dispose() {
    for (SolverContext ctx : solvers) {
      ctx.dispose();
    }
    for (SolverContext ctx : direct) {
      ctx.dispose();
    }
  }
}
