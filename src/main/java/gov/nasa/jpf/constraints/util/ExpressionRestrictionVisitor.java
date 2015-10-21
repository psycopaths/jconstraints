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
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;

class ExpressionRestrictionVisitor extends AbstractExpressionVisitor<Expression<?>,Predicate<? super Variable<?>>> {
  
  private static final ExpressionRestrictionVisitor INSTANCE = new ExpressionRestrictionVisitor();
  
  public static ExpressionRestrictionVisitor getInstance() {
    return INSTANCE;
  }
  
  //private boolean mixedParams = false;

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(Variable<E> v, Predicate<? super Variable<?>> data) {
    return (data.apply(v)) ? v : null;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.QuantifierExpression, java.lang.Object)
   */
  @Override
  public Expression<?> visit(QuantifierExpression q, Predicate<? super Variable<?>> data) {
    Predicate<Variable<?>> newPred = Predicates.or(Predicates.in(q.getBoundVariables()), data);
    Expression<?> exp = visit(q.getBody(), newPred);
    return (exp != null) ? q.duplicate(new Expression[]{exp}) : null;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#defaultVisit(gov.nasa.jpf.constraints.api.Expression, java.lang.Object)
   */
  @Override
  protected <E> Expression<?> defaultVisit(Expression<E> expression,
      Predicate<? super Variable<?>> data) {
    Expression<?>[] children = expression.getChildren();
    if(children.length == 0)
      return expression;
    
    Expression<?> c1 = children[0];
    Expression<?> v1 = visit(c1, data);
    
    if(children.length == 1)
      return (v1 != null) ? expression.duplicate(new Expression[]{v1}) : null;
    
    Expression<?> c2 = children[1];
    Expression<?> v2 = visit(c2, data);
    if(v1 == c1 && v2 == c2)
      return expression;
    
    if(v1 == null) {
      if(v2 != null && ExpressionUtil.containsVars(v2))
        throw new MixedParamsException();
      return null;
    }
    if(v2 == null) {
      if(ExpressionUtil.containsVars(v1))
        throw new MixedParamsException();
      return null;
    }
    
    return expression.duplicate(new Expression[]{v1, v2});
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.PropositionalCompound, java.lang.Object)
   */
  @Override
  @SuppressWarnings("unchecked")
  public Expression<?> visit(PropositionalCompound n, Predicate<? super Variable<?>> data) {
    Expression<Boolean> c1 = n.getLeft();
    Expression<Boolean> v1 = (Expression<Boolean>)visit(c1, data);
    
    Expression<Boolean> c2 = n.getRight();
    Expression<Boolean> v2 = (Expression<Boolean>)visit(c2, data);
    if(v1 == c1 && v2 == c2)
      return n;
    
    if(v1 == null)
      return v2;
    if(v2 == null)
      return v1;
    
    return new PropositionalCompound(v1, n.getOperator(), v2);
  }
  
//  public boolean hasMixedParams() {
//    return mixedParams;
//  }
  

  @SuppressWarnings("unchecked")
  public <T> Expression<T> apply(Expression<T> expr, Predicate<? super Variable<?>> pred) {
    return (Expression<T>)visit(expr, pred);
  }
  
}
