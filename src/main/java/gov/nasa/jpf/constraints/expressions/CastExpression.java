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
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

/**
 * cast between numbers
 */
public class CastExpression<F,E> extends AbstractExpression<E> {
  
  
  public static <F,E>
  CastExpression<F,E> create(Expression<F> casted, Type<E> toType) {
    CastOperation<? super F, ? extends E> castOp = toType.cast(casted.getType());
    return new CastExpression<F,E>(casted, toType, castOp);
  }
  
  public static <F,E>
  CastExpression<F,E> create(Expression<F> casted, Type<E> toType, CastOperation<? super F, ? extends E> castOp) {
    return new CastExpression<F,E>(casted, toType, castOp);
  }

  private final Expression<F> casted;
  private final Type<E> toType;
  private final CastOperation<? super F, ? extends E> castOp;
  
  public CastExpression(Expression<F> casted, Type<E> toType, CastOperation<? super F, ? extends E> castOp) {
    this.casted = casted;
    this.toType = toType;
    this.castOp = castOp;
  }
  
  
  @Override
  public E evaluate(Valuation values) {
    F f = casted.evaluate(values);
    return castOp.cast(f);
  }


  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.casted.collectFreeVariables(variables);
  }

  @Override
  public Type<E> getType() {
    return this.toType;
  }
  
  public Expression<F> getCasted() {
    return this.casted;
  }


  @Override
  @SuppressWarnings("unchecked")
  public Expression<F>[] getChildren() {
    return new Expression[]{casted};
  }


  @Override
  public Expression<E> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 1;
    
    Expression<?> newCasted = newChildren[0];
    if(newCasted == casted)
      return this;
    
    return CastExpression.create(newCasted.requireAs(casted.getType()), toType, castOp);
  }


  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(');
    a.append(toType.getName());
    a.append(')');
    casted.print(a, flags);
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) 
          throws IOException {
    a.append('(');
    if(toType == null){
      a.append("null");
    }else{
      a.append(toType.getName());
    }
    a.append(')');
    if(casted == null){
      a.append("null");
    } else {
      casted.print(a, flags);
    }
  }
  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((castOp == null) ? 0 : castOp.hashCode());
    result = prime * result + ((casted == null) ? 0 : casted.hashCode());
    result = prime * result + ((toType == null) ? 0 : toType.hashCode());
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
    CastExpression<?,?> other = (CastExpression<?,?>) obj;
    if (castOp == null) {
      if (other.castOp != null)
        return false;
    } else if (!castOp.equals(other.castOp))
      return false;
    if (casted == null) {
      if (other.casted != null)
        return false;
    } else if (!casted.equals(other.casted))
      return false;
    if (toType == null) {
      if (other.toType != null)
        return false;
    } else if (!toType.equals(other.toType))
      return false;
    return true;
  }

  

}
