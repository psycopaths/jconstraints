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
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

/**
 * numeric unary minus
 */
public class UnaryMinus<E> extends AbstractExpression<E> {

  public static <E> UnaryMinus<E> create(
      Expression<E> negated) {
    return new UnaryMinus<E>(negated);
  }
  
  private final Expression<E> negated;

  public UnaryMinus(Expression<E> negated) {
    this.negated = negated;
  }
  
  public Expression<E> getNegated() {
    return this.negated;
  }
  
  @Override
  public E evaluate(Valuation values) {
    E num = negated.evaluate(values);
    NumericType<E> type = (NumericType<E>)getType();
    return type.negate(num);
  }    
    
  
  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    this.negated.collectFreeVariables(variables);
  }

  
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + negated.hashCode();
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    UnaryMinus<?> other = (UnaryMinus<?>) obj;
    return negated.equals(other.negated);
  }

  public Type<E> getType() {
    return negated.getType();
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[]{negated};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 1;
    
    if(negated == newChildren[0])
      return this;
    
    return UnaryMinus.create(newChildren[0]);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("-(");
    negated.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException{
    a.append("-(");
    if(negated == null){
      a.append("null");
    } else {
      negated.print(a, flags);
    }
    a.append(')');
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }
}