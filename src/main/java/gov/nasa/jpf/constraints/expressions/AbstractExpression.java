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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.types.Type;

public abstract class AbstractExpression<E>
    extends Expression<E> {
  
  
  protected static boolean identical(Expression<?>[] newChildren, Expression<?> thisChild) {
    if(newChildren.length != 1)
      return false;
    return thisChild == newChildren[0];
  }
  
  protected static boolean identical(Expression<?>[] newChildren, Expression<?> ...thisChildren) {
    if(newChildren.length != thisChildren.length)
      return false;
    for(int i = 0; i < thisChildren.length; i++) {
      if(newChildren[i] != thisChildren[i])
        return false;
    }
    return true;
  }
  
  @SuppressWarnings("unchecked")
  protected static <E> Expression<E>[] requireAs(Expression<?>[] expressions, Type<E> type) {
    for(int i = 0; i < expressions.length; i++)
      expressions[i].requireAs(type);
    return (Expression<E>[])expressions;
  }
 
}
