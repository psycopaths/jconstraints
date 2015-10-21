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
package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;

public class NestingDepthVisitor extends
    AbstractExpressionVisitor<Integer, Void> {
  
  private static final NestingDepthVisitor INSTANCE = new NestingDepthVisitor();
  
  public static NestingDepthVisitor getInstance() {
    return INSTANCE;
  }
  
  
  
  @SafeVarargs
  private final int maxDepth(Expression<?> ...children) {
    if(children.length == 0)
      return 0;
    
    int maxDepth = children[0].accept(this, null);
    for(int i = 1; i < children.length; i++) {
      int d = visit(children[i], null);
      if(d > maxDepth)
        maxDepth = d;
    }
    return maxDepth;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.functions.FunctionExpression, java.lang.Object)
   */
  @Override
  public <E> Integer visit(FunctionExpression<E> f, Void data) {
    return 1 + maxDepth(f.getChildren());
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#defaultVisit(gov.nasa.jpf.constraints.api.Expression, java.lang.Object)
   */
  @Override
  protected <E> Integer defaultVisit(Expression<E> expression, Void data) {
    return maxDepth(expression.getChildren());
  }
  
  
  public int apply(Expression<?> expr) {
    return visit(expr, null);
  }

  

}
