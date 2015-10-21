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
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;

public class ContainsVarsVisitor extends
    AbstractExpressionVisitor<Boolean, Void> {
  
  private static ContainsVarsVisitor INSTANCE = new ContainsVarsVisitor();
  
  public static ContainsVarsVisitor getInstance() {
    return INSTANCE;
  }
  
  
  protected ContainsVarsVisitor() {
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, java.lang.Object)
   */
  @Override
  public <E> Boolean visit(Variable<E> v, Void data) {
    return Boolean.TRUE;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#defaultVisit(gov.nasa.jpf.constraints.api.Expression, java.lang.Object)
   */
  @Override
  protected <E> Boolean defaultVisit(Expression<E> expression, Void data) {
    Expression<?>[] children = expression.getChildren();
    
    for(int i = 0; i < children.length; i++) {
      if(visit(children[i], null))
        return Boolean.TRUE;
    }
    
    return Boolean.FALSE;
  }
  
  public boolean apply(Expression<?> exp) {
    return visit(exp, null).booleanValue();
  }


}
