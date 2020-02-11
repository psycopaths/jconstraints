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

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.BoolExpr;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.QuantifierEliminator;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import java.util.Collections;
import java.util.Map;

import com.microsoft.z3.Context;
import com.microsoft.z3.Global;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Tactic;
import com.microsoft.z3.Z3Exception;
import gov.nasa.jpf.constraints.api.Simplifier;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashMap;
import java.util.Map.Entry;
import java.util.logging.Logger;

public class NativeZ3Solver extends ConstraintSolver
        implements QuantifierEliminator, Simplifier<Boolean> {

  private static final Logger logger = Logger.getLogger("constraints");
    
  private Context ctx;

  private NativeZ3SolverContext defaultContext;

  private final int timeout;

  private final Map<String, String> options;

  static {
    // This has to be set globally
    // TODO: this should be moved to options as well
    Global.setParameter("smt.bv.enable_int2bv", "true");
  }

  public NativeZ3Solver() {
    this(-1, new HashMap<String, String>());
  }

  public NativeZ3Solver(int to, Map<String, String> properties) {
    //super.name = "Z3";

    this.timeout = to;
    this.options = properties;

    Map<String, String> cfg = Collections.singletonMap("model", "true");
    for (Entry<String, String> o : options.entrySet()) {
    	Global.setParameter(o.getKey(), o.getValue());
      
    }
    try {
      this.ctx = new Context(cfg);
      defaultContext = createContext();
    } catch (Z3Exception ex) {
      if (ctx != null) {
        try {
          //ctx.dispose();
        } catch (Throwable t) {
        }
      }
      throw new RuntimeException(ex);
    }
  }

  Context getContext() {
    return ctx;
  }

  public void dispose() {
    defaultContext.dispose();
    defaultContext = null;
    //ctx.dispose();
    ctx = null;
  }

  protected void finalize() throws Throwable {
    super.finalize();
    if (ctx != null) {
      dispose();
    }
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    try {
      defaultContext.push();
      defaultContext.add(f);
      return defaultContext.solve(result);
    } finally {
      defaultContext.pop();
    }
  }

  @Override
  public NativeZ3SolverContext createContext() {
    Solver solver = null;

    try {
      solver = ctx.mkSolver();
      NativeZ3ExpressionGenerator root;

      if (timeout > 0) {
        Params p = ctx.mkParams();
        //p.add("timeout",timeout);
        //p.add(":timeout", timeout); 
        p.add("timeout", timeout);
        solver.setParameters(p);
      }

      root = new NativeZ3ExpressionGenerator(ctx, solver);

      return new NativeZ3SolverContext(solver, root);
    } catch (Z3Exception ex) {
      if (solver != null) {
        try {
          //solver.dispose();
        } catch (Throwable t) {
        }
      }
      throw new RuntimeException(ex);
    }
  }

  @Override
  public Expression<?> eliminateQuantifiers(Expression<Boolean> expr) {
    Solver solver = ctx.mkSolver();
    NativeZ3ExpressionGenerator rootGenerator
            = new NativeZ3ExpressionGenerator(ctx, solver);
    Tactic tactic = ctx.mkTactic("qe");
    //The booleans are model genertation, unsat core, proof generation
    Goal goal = ctx.mkGoal(true, false, false);

    BoolExpr z3Expr = rootGenerator.generateAssertion(expr);
    goal.add(z3Expr);

    ApplyResult res = tactic.apply(goal);
    Goal[] subgoals = res.getSubgoals();
    return convertSubgoals(subgoals);
  }
  
  @Override
  public Expression<Boolean> simplify(Expression<Boolean> expr) {
    Solver solver = ctx.mkSolver();
    NativeZ3ExpressionGenerator rootGenerator
            = new NativeZ3ExpressionGenerator(ctx, solver);
    
    Tactic tactic = ctx.mkTactic("ctx-solver-simplify");
    Goal goal = ctx.mkGoal(true, false, false);
    
    BoolExpr z3Expr = rootGenerator.generateAssertion(expr);
    goal.add(z3Expr);
    
    ApplyResult res = tactic.apply(goal);    
    if (res.getNumSubgoals() == 1 && 
            (res.getSubgoals()[0].isDecidedSat() || 
            res.getSubgoals()[0].isDecidedUnsat())) {
        
        logger.warning("Simplification failed.");
        return expr;
    }
    
    Goal[] subgoals = res.getSubgoals();
    return convertSubgoals(subgoals);    
  }
  
  private Expression<Boolean> convertSubgoals(Goal[] subgoals) {
    Expression<Boolean> result = null;
    NativeZ3TojConstraintConverter converter = new NativeZ3TojConstraintConverter();
    for (Goal g : subgoals) {
      BoolExpr[] formulas = g.getFormulas();
      for (BoolExpr f : formulas) {
        Expression<Boolean> jConstraintExpr = converter.parse(f);
        result = (result == null) ? jConstraintExpr
                : ExpressionUtil.and(result, jConstraintExpr);
      }
    }
    return result;      
  }
  
}
