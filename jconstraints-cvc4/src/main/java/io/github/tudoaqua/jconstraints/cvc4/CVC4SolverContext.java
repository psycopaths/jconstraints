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

package io.github.tudoaqua.jconstraints.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Result;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class CVC4SolverContext extends SolverContext {

  private ExprManager em;
  private SmtEngine ctx;

  private HashMap<Variable, Expr> vars;
  private LinkedList<HashMap<Variable, Expr>> varsHistory;

  public CVC4SolverContext() {
    em = new ExprManager();
    ctx = new SmtEngine(em);
    ctx.setOption("produce-models", new SExpr(true));
    ctx.setOption("output-language", new SExpr("cvc4"));
    ctx.setOption("strings-exp", new SExpr(true));
    ctx.setOption("seed", new SExpr(1234));
    ctx.setOption("random-seed", new SExpr(1234));
    vars = new HashMap<>();
    varsHistory = new LinkedList<>();
    varsHistory.push(new HashMap());
  }

  @Override
  public void push() {
    ctx.push();
    varsHistory.push(new HashMap(vars));
  }

  @Override
  public void pop() {
    ctx.pop();
    vars = varsHistory.pop();
  }

  @Override
  public void pop(int i) {
    for (int j = 0; j < i; j++) {
      this.pop();
    }
  }

  /** The valuation is only filled with data, if the expressions in the context are satisfiable. */
  @Override
  public ConstraintSolver.Result solve(Valuation valuation) {
    Result res = ctx.checkSat();
    if (res.toString().toLowerCase().equals("sat")) {
      CVC4Solver.getModel(valuation, vars, ctx);
    }
    return CVC4Solver.convertCVC4Res(res);
  }

  @Override
  public void add(List<Expression<Boolean>> list) {
    CVC4ExpressionGenerator gen = new CVC4ExpressionGenerator(em, vars);
    for (Expression<Boolean> l : list) {
      Expr expr = gen.generateExpression(l);
      ctx.assertFormula(expr);
    }
    vars = gen.getVars();
  }

  @Override
  public void dispose() {
    ctx.delete();
  }
}
