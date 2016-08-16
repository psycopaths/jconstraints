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
package gov.nasa.jpf.constraints.expressions.functions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpression;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

public class FunctionExpression<T> extends AbstractExpression<T> {
  
  private final Function<T> function;
  private final Expression<?>[] args;
  
  
  public FunctionExpression(Function<T> function, Expression<?> ...args) {
	  if(function.getArity() != args.length) {
		  throw new IllegalArgumentException("Cannot invoke function " + function.getName() + " of arity "
				  + function.getArity() + " with " + args.length + " arguments");
		  
		  // TODO parameter type check?
	  }
    this.function = function;
    this.args = args;
  }
  
  
  @Override
  public T evaluate(Valuation values) {
	  Object[] argValues = new Object[args.length];
	  for(int i = 0; i < args.length; i++) {
		  argValues[i] = args[i].evaluate(values);
	  }
	  return function.evaluate(argValues);
  }
  
  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    for(Expression<?> a : args)
      a.collectFreeVariables(variables);
  }
  
  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }
  
  @Override
  public Type<T> getType() {
    return function.getReturnType();
  }
  
  @Override
  public Expression<?>[] getChildren() {
    return args.clone();
  }
  
  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    Type<?>[] ptypes = function.getParamTypes();
    assert ptypes.length == newChildren.length;
    
    for(int i = 0; i < ptypes.length; i++) {
      assert ptypes[i].equals(newChildren[i].getType());
    }
    
    return new FunctionExpression<>(function, newChildren);
  }
  
  @Override
  public void print(Appendable a, int flags) throws IOException {
    boolean qid = Expression.quoteIdentifiers(flags);
    if(qid)
      a.append('\'');
    a.append(function.getName());
    if(qid)
      a.append('\'');
    a.append('(');
    boolean first = true;
    for(Expression<?> arg : args) {
      if(first)
        first = false;
      else
        a.append(',');
      arg.print(a, flags);
    }
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    boolean qid = Expression.quoteIdentifiers(flags);
    if(qid)
      a.append('\'');
    if(function == null){
      a.append("null");
    } else {
      a.append(function.getName());
    }
    if(qid)
      a.append('\'');
    a.append('(');
    boolean first = true;
    for(Expression<?> arg : args) {
      if(first)
        first = false;
      else
        a.append(',');
      if(arg != null){
        a.append("null");
      } else {
        arg.print(a, flags);
      }
    }
    a.append(')');
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + Arrays.hashCode(args);
    result = prime * result + ((function == null) ? 0 : function.hashCode());
    return result;
  }


  /* (non-Javadoc)
   * @see java.lang.Object#equals(java.lang.Object)
   */
  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    FunctionExpression<?> other = (FunctionExpression<?>) obj;
    if (!Arrays.equals(args, other.args))
      return false;
    if (function == null) {
      if (other.function != null)
        return false;
    } else if (!function.equals(other.function))
      return false;
    return true;
  }

    public Function<T> getFunction() {
        return function;
    }

    public Expression<?>[] getArgs() {
        return args;
    }
}
