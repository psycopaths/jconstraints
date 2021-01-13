/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

public class ProcessWrapperContext extends SolverContext {

  private final ProcessWrapperSolver solver;
  private Stack<List<Expression>> stack;
  private List<Expression> current;

  public ProcessWrapperContext(String name) {
    solver = new ProcessWrapperSolver(name);
    init();
  }

  public ProcessWrapperContext(String name, String javaBinary) {
    solver = new ProcessWrapperSolver(name, javaBinary);
    init();
  }

  private void init() {
    stack = new Stack<>();
    current = new LinkedList<>();
  }

  public String getName() {
    return solver.getName();
  }

  @Override
  public void push() {
    stack.push(current);
    current = new LinkedList<>();
  }

  @Override
  public void pop(int n) {
    for (int i = 0; i < n; i++) {
      current = stack.pop();
    }
  }

  @Override
  public Result solve(Valuation val) {
    Expression test = getCurrentExpression();
    Result res = solver.solve(test, val);
    //    if (res.equals(Result.SAT)) {
    //      assert (Boolean) test.evaluate(val);
    //    }
    return res;
  }

  public Expression getCurrentExpression() {
    Expression test = ExpressionUtil.TRUE;
    for (List<Expression> list : stack) {
      for (Expression e : list) {
        test = ExpressionUtil.and(test, e);
      }
    }
    for (Expression e : current) {
      test = ExpressionUtil.and(test, e);
    }
    return test;
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    current.addAll(expressions);
  }

  @Override
  public void dispose() {
    stack = new Stack<>();
    current = new LinkedList<>();
  }
}
