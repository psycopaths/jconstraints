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
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

public class BitvectorNegation<E>
    extends AbstractExpression<E> {
  
  public static <E> BitvectorNegation<E> create(Expression<E> expression) {
    return new BitvectorNegation<E>(expression);
  }

  private final Expression<E> negated;
  
  public BitvectorNegation(Expression<E> negated) {
    assert negated.getType() instanceof BVIntegerType;
    
    this.negated = negated;
  }

  @Override
  public E evaluate(Valuation values) {
    BVIntegerType<E> type = (BVIntegerType<E>)getType();
    E value = negated.evaluate(values);
    return type.negate(value);
  }
  
  public Expression<E> getNegated() {
    return negated;
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    negated.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Type<E> getType() {
    return negated.getType();
  }

  @Override
  @SuppressWarnings("unchecked")
  public Expression<E>[] getChildren() {
    return new Expression[]{negated};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 1;
    if(identical(newChildren, negated))
      return this;
    return create(newChildren[0]);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('~');
    negated.print(a, flags);
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) 
          throws IOException{
    a.append('~');
    if(negated != null){
      negated.print(a, flags);
    } else {
      a.append("null");
    }
  }
  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((negated == null) ? 0 : negated.hashCode());
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
    BitvectorNegation<?> other = (BitvectorNegation<?>) obj;
    if (negated == null) {
      if (other.negated != null)
        return false;
    } else if (!negated.equals(other.negated))
      return false;
    return true;
  }
  
  

}
