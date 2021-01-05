/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377
 * the original license is:
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
 *
 * Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues
 * under Apache 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.api;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import java.util.Arrays;
import java.util.List;

/** Solver context to support incremental solving (i.e., with backtracking). */
public abstract class SolverContext {

  public abstract void push();

  public abstract void pop(int n);

  public void pop() {
    pop(1);
  }

  public Result isSatisfiable() {
    return solve(null);
  }

  public abstract Result solve(Valuation val);

  @SafeVarargs
  public final void add(Expression<Boolean>... expressions) {
    add(Arrays.asList(expressions));
  }

  public abstract void add(List<Expression<Boolean>> expressions);

  public Result isSatisfiable(Expression<Boolean> expr) {
    push();
    add(expr);
    Result res = isSatisfiable();
    pop();
    return res;
  }

  public Result solve(Expression<Boolean> expr, Valuation val) {
    push();
    add(expr);
    Result res = solve(val);
    pop();
    return res;
  }

  public Result[] whichSatisfiable(List<Expression<Boolean>> expressions) {
    Result[] results = new Result[expressions.size()];
    int i = 0;
    for (Expression<Boolean> expr : expressions) {
      push();
      add(expr);
      Result res = isSatisfiable();
      pop();
      results[i++] = res;
    }
    return results;
  }

  public abstract void dispose();
}
