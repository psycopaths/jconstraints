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
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperContext;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import gov.nasa.jpf.constraints.solvers.encapsulation.SolvingResult;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

public class PortfolioSolver extends ConstraintSolver {

  private List<ConstraintSolver> processWrappedSolvers;
  private List<ConstraintSolver> directSolvers;
  private ExecutorService exec;
  private boolean isProcessSolverDisabled = false;

  public PortfolioSolver(Properties properties) {
    processWrappedSolvers = new LinkedList();
    directSolvers = new LinkedList<>();
    resolveSolvers(properties);
    exec = null;
  }

  public static Result processResult(
      int maxSolvers, ExecutorCompletionService ecs, Valuation valuation) {
    for (int i = 0; i < maxSolvers; i++) {
      try {
        Future<SolvingResult> solverRes = ecs.take();
        if (solverRes.isDone()) {
          SolvingResult solvingRes = solverRes.get();
          Result res = solvingRes.getResult();
          if (!res.equals(Result.DONT_KNOW)) {
            if (res.equals(Result.SAT)) {
              for (ValuationEntry e : solvingRes.getVal().entries()) {
                valuation.addEntry(e);
              }
            }
            return res;
          }
        }
      } catch (InterruptedException e) {
        e.printStackTrace();
      } catch (ExecutionException e) {
        e.printStackTrace();
      }
    }
    return Result.DONT_KNOW;
  }

  @Override
  public Result solve(Expression<Boolean> expression, Valuation valuation) {
    StringOrFloatExpressionVisitor visitor = new StringOrFloatExpressionVisitor();
    boolean isStringOrFloatExpression = expression.accept(visitor, null);
    if (!isProcessSolverDisabled && isStringOrFloatExpression) {
      List<ConstraintSolver> solvers = new LinkedList<>();
      for (ConstraintSolver solver : processWrappedSolvers) {
        if (solver.getName().equalsIgnoreCase("cvc4")) {
          solvers.add(solver);
        }
      }
      Result res = dispatcheProcessWrappedSolvers(expression, valuation, solvers);
      if(res.equals(Result.SAT)){
        try{
          boolean evaluation = expression.evaluateSMT(valuation);
          if(!evaluation){
            res = Result.DONT_KNOW;
          }
        } catch (Exception e){
          res = Result.DONT_KNOW;
        }
      }
      if (!res.equals(Result.DONT_KNOW)) {
        return res;
      } else {
        isProcessSolverDisabled = true;
        System.out.println("Disable process solver and shutdown exec");
        exec.shutdownNow();
        return solve(expression, valuation);
      }
    } else {
      for (ConstraintSolver solver : directSolvers) {
        if (solver.getName().equalsIgnoreCase("z3")) {
          return solver.solve(expression, valuation);
        }
      }
    }
    throw new IllegalArgumentException("Cannot run the problem with the provided solvers");
  }

  @Override
  public SolverContext createContext() {
    Map<String, String> env = System.getenv();
    List<ProcessWrapperContext> ctxs = new LinkedList<>();
    for (ConstraintSolver s : processWrappedSolvers) {
      ctxs.add((ProcessWrapperContext) s.createContext());
    }
    List<SolverContext> direct = new LinkedList<>();
    for (ConstraintSolver s : directSolvers) {
      direct.add(s.createContext());
    }
    return new PortfolioSolverContext(ctxs, direct);
  }

  private Result dispatcheProcessWrappedSolvers(
      Expression<Boolean> expression, Valuation valuation, List<ConstraintSolver> solvers) {
    List<Runnable> calls = new LinkedList<>();
    if (exec == null) {
      exec = Executors.newFixedThreadPool(processWrappedSolvers.size());
    }
    ExecutorCompletionService ecs = new ExecutorCompletionService(exec);
    for (ConstraintSolver solver : solvers) {
      ecs.submit(
          () -> {
            Valuation val = new Valuation();
            Result res = solver.solve(expression, val);
            return new SolvingResult(res, val);
          });
    }
    return processResult(solvers.size(), ecs, valuation);
  }

  private void resolveSolvers(Properties properties) {
    String specifiedSolvers = properties.getProperty("jdart.portfolio.solvers", "");
    String javaBinary = properties.getProperty("jdart.portfolio.java", "");
    ConstraintSolverFactory csf = ConstraintSolverFactory.getRootFactory();
    String[] solverNames = specifiedSolvers.split(",");
    for (String solverName : solverNames) {
      processWrappedSolvers.add(new ProcessWrapperSolver(solverName, javaBinary));
      if (!solverName.equalsIgnoreCase("cvc4")) {
        directSolvers.add(csf.createSolver(solverName));
      }
    }
  }
}
