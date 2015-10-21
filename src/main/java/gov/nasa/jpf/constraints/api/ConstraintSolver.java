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

package gov.nasa.jpf.constraints.api;


/**
 * Abstract superclass for constraint solvers.
 */
public abstract class ConstraintSolver {
  
  /**
   * result returned by a constraint solver
   * 
   */
  public static enum Result {SAT,UNSAT,DONT_KNOW};
  
  /**
   * runs f by the constraint solver and returns if
   * f can be satisfied
   * 
   * @param f formula to check for satisfiability
   * @return the satisfiability {@link Result} 
   */
  public Result isSatisfiable(Expression<Boolean> f) {
    return solve(f, new Valuation());
  }
  
  
  /**
   * solves f and returns a satisfying solution
   * 
   * @param f 
   * @param result solution that satisfies f or null in case of only checking for satisfiability
   * @return the satisfiability {@link Result}
   */
  public abstract Result solve(Expression<Boolean> f, Valuation result);

  /**
   * Create a solver context, which allows for incremental solving (i.e., via push and pop).
   * This is an optional operation.
   * @return a solver context
   * @throws UnsupportedOperationException if the solver engine does not incremental solving
   */
  public SolverContext createContext() {
	  throw new UnsupportedOperationException("Solver does not support incremental solving");
  }
  
  
  // LEGACY API
  
  @Deprecated
  public Result isSatisfiable(Expression<Boolean> f, MinMax m) {
    return solve(f, m, new Valuation());
  }
  
  @Deprecated
  public Result solve(Expression<Boolean> f, MinMax m, Valuation val) {
    //Expression<Boolean> mod = m.apply(f);
    return solve(f, val);
  }
    
}
