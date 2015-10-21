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
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.AbstractPrintable;

import java.io.IOException;

import com.google.common.base.Joiner;

public class Function<T> extends AbstractPrintable {
  
  private final String name;
  private final Type<T> returnType;
  private final Type<?>[] paramTypes;

  @SafeVarargs
  public Function(String name, Type<T> returnType, Type<?> ...paramTypes) {
    this.name = name;
    this.returnType = returnType;
    this.paramTypes = paramTypes;
  }
  
  
  public String getName() {
    return name;
  }
  
  public Type<T> getReturnType() {
    return returnType;
  }
  
  public Type<?>[] getParamTypes() {
    return paramTypes;
  }
  
  public FunctionExpression<T> toExpression(Expression<?> ...args) {
	  return new FunctionExpression<>(this, args);
  }
  
  public T evaluate(Object... args) {
	  throw new UnsupportedOperationException("Semantics for function '" + name + "' undefined");
  }
  
  public int getArity() {
	  return paramTypes.length;
  }


  @Override
  public void print(Appendable a) throws IOException {
    a.append(name).append('(');
    Joiner.on(',').appendTo(a, paramTypes);
    a.append("):").append(returnType.toString());
  }

}
