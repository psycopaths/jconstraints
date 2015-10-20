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

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import gov.nasa.jpf.constraints.util.TypeUtil;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;

public class NativeZ3SolverContext extends SolverContext {
	
	private static final Logger logger = Logger.getLogger("constraints");
	
	private final Deque<NativeZ3ExpressionGenerator> generatorStack
		= new ArrayDeque<NativeZ3ExpressionGenerator>();
	private final Deque<Map<String,Variable<?>>> freeVarsStack
		= new ArrayDeque<Map<String,Variable<?>>>();
	
	private Solver solver;

	public NativeZ3SolverContext(Solver solver, NativeZ3ExpressionGenerator rootGenerator) {
		this.solver = solver;
		this.generatorStack.push(rootGenerator);
		this.freeVarsStack.push(new HashMap<String,Variable<?>>());
	}
	
	@Override
	public void push() {
		try {
			solver.push();
			Map<String,Variable<?>> fvMap = freeVarsStack.peek();
			generatorStack.push(generatorStack.peek().createChild());
			freeVarsStack.push(new HashMap<String,Variable<?>>(fvMap));
		}
		catch(Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public void pop(int n) {
		for(int i = 0; i < n; i++) {
			NativeZ3ExpressionGenerator gen = generatorStack.pop();
			gen.dispose();
			freeVarsStack.pop();
		}
		try {
      solver.pop(n);
    }
    catch(Z3Exception ex) {
      throw new RuntimeException(ex);
    }
	}

	@Override
	public Result solve(Valuation val) {
	  logger.finer("Solving ...");
		try {
			Status status = solver.check();
			if(status != Status.SATISFIABLE || val == null) {
			  logger.finer("Not satisfiable: " + status);
                            
                                if (status == Status.UNSATISFIABLE) {
                                    logger.finest("unsat core: ");
                                      for (Expr e : solver.getUnsatCore()) {
                                          logger.finest("  " + e.getSExpr());
                                      }
                                }
                          
				return translateStatus(status);
			}
			
			Model model = solver.getModel();
			try {
			    if(logger.isLoggable(Level.FINE)) {
				    String modelText = model.toString().replace("\n", ", ").trim();
				    logger.fine(modelText);
			    }
			    
			    NativeZ3ExpressionGenerator gen = generatorStack.peek();
			    if(gen.isTainted(model)) {
			      model.dispose();
			      logger.info("Model is tainted, rechecking ...");
			      model = gen.recheckUntainted();
			      if(model == null)
			        return Result.DONT_KNOW;
			    }
			    
			    Map<String,Variable<?>> freeVars = new HashMap<String,Variable<?>>(freeVarsStack.peek());
			    
		        
			    // FIXME mi: using origVars here fixes the issue that variables occuring only in the
			    //           scope of quantifiers are part of the valuation. Might it break something
			    //           else?
			    long max = model.getNumConsts();
			    FuncDecl[] decls = model.getConstDecls();
			    try {
			    	for (int i = 0; i < max; i++) { 
			    		FuncDecl decl = decls[i];
			    		
			    		Symbol sym = null;
			    		String text = null;
			    		try {
			    			sym = decl.getName();
			    			text = sym.toString().trim();
			    		}
			    		finally {
			    			sym.dispose();
			    		}
			    		
					    Variable<?> v = freeVars.get(text);
					    
					    if (v == null) {
					    	continue;
					    }
					    freeVars.remove(text);

			
					    AST res = model.getConstInterp(decl);
					    try {				        
					    	String value = res.toString().trim();
					    	if(TypeUtil.isRealSort(v) && value.contains("/")) {
					    	  String[] split = value.split("/");
					    	  BigDecimal nom = new BigDecimal(split[0].trim());
					    	  BigDecimal den = new BigDecimal(split[1].trim());
					    	  BigDecimal quot = nom.divide(den, 10, RoundingMode.FLOOR);
					    	  
                  val.setParsedValue(v, quot.toPlainString());
					    	}
					    	else
					    	  val.setParsedValue(v, value);
						}
					    finally {
						    res.dispose();
						}
				    }
			    }
			    finally {
			    	for(int i = 0; i < decls.length; i++)
			    		decls[i].dispose();
			    }
			    
		    
			    for (Variable<?> r : freeVars.values())
				    val.setDefaultValue(r);
			    
			}
			finally {
				model.dispose();
			}
			
			logger.finer("Satisfiable, valuation " + val);
			return Result.SAT;
		}
		catch(Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	
	
	public void dispose() {
		while(!generatorStack.isEmpty())
			generatorStack.pop().dispose();
		freeVarsStack.clear();
		
		try {
			solver.dispose();
		}
		catch(Z3Exception ex) {}
		finally {
			solver = null;
		}
	}
	
	protected void finalize() throws Throwable {
		super.finalize();
		
		if(solver != null)
			dispose();
	}
	
	@Override
	public void add(List<Expression<Boolean>> expressions) {
		BoolExpr[] exprs = new BoolExpr[expressions.size()];
		
		NativeZ3ExpressionGenerator gen = generatorStack.peek();
		
		Map<String,Variable<?>> fvMap = freeVarsStack.peek();
		
		int i = 0;
		try {
			for(Expression<Boolean> ex : expressions) {
			  //logger.finer("Checking " + ex);
				exprs[i++] = gen.generateAssertion(ex);
				Set<Variable<?>> fvs = ExpressionUtil.freeVariables(ex);
				for(Variable<?> v : fvs) 
					fvMap.put(v.getName(), v);
			}
			
			solver.add(exprs);
		}
		catch(Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
		  // !!! This is a very important corner case. Sometimes, the expression
		  // might just be a single boolean variable, WHICH MAY BE PROTECTED!
		  gen.safeDispose(exprs);
		}
	}

	
	private static Result translateStatus(Status status) {
		switch (status) {
		case SATISFIABLE:
			return Result.SAT;
		case UNSATISFIABLE:
			return Result.UNSAT;
		default: // case UNKNOWN:
			return Result.DONT_KNOW;
		}
	}

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
            try {
                for (BoolExpr e : this.solver.getAssertions()) {
                    sb.append(e.getSExpr()).append("\n");
                }   } catch (Z3Exception ex) {
                    sb.append("Error: ").append(ex.getMessage());
            }
        return sb.toString();
    }


        
}
