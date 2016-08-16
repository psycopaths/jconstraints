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
import gov.nasa.jpf.constraints.types.BuiltinTypes;

import java.io.IOException;
import java.util.Collection;

/**
 * propositional compound expression
 */
public class PropositionalCompound extends AbstractBoolExpression {
  
  private final Expression<Boolean> left;
  private final LogicalOperator operator;
  private final Expression<Boolean> right;

  public PropositionalCompound(Expression<Boolean> left, LogicalOperator operator, Expression<Boolean> right) {
    this.operator = operator;
    this.left = left;
    this.right = right;
  }
  

  @Override
  public Boolean evaluate(Valuation values) {
    boolean lv = left.evaluate(values);
    boolean rv = right.evaluate(values);
    
    return operator.eval(lv, rv);
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    left.collectFreeVariables(variables);
    right.collectFreeVariables(variables);
  }
  
  public Expression<Boolean> getLeft() {
    return left;
  }
  
  public Expression<Boolean> getRight() {
    return right;
  }


  /**
   * @return the operator
   */
  public LogicalOperator getOperator() {
    return operator;
  }


  @Override
  @SuppressWarnings("unchecked")
  public Expression<Boolean>[] getChildren() {
    return new Expression[]{left, right};
  }


  @Override
  public Expression<Boolean> duplicate(
      Expression<?>[] newChildren) {
    assert newChildren.length == 2;
    
    if(identical(newChildren, left, right))
      return this;
    
    return new PropositionalCompound(newChildren[0].as(BuiltinTypes.BOOL), operator, newChildren[1].as(BuiltinTypes.BOOL));
  }


  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(');
    left.print(a, flags);
    a.append(' ').append(operator.toString()).append(' ');
    right.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) 
          throws IOException {
    a.append('(');
    if(left == null){
      a.append("null");
    }else{
      left.printMalformedExpression(a, flags);
    }
    a.append(' ').append(operator.toString()).append(' ');
    if(right == null){
      a.append("null");
    }else{
      right.printMalformedExpression(a, flags);
    }
    a.append(')');
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
    result = prime * result + ((left == null) ? 0 : left.hashCode());
    result = prime * result + ((operator == null) ? 0 : operator.hashCode());
    result = prime * result + ((right == null) ? 0 : right.hashCode());
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
    PropositionalCompound other = (PropositionalCompound) obj;
    if (left == null) {
      if (other.left != null)
        return false;
    } else if (!left.equals(other.left))
      return false;
    if (operator != other.operator)
      return false;
    if (right == null) {
      if (other.right != null)
        return false;
    } else if (!right.equals(other.right))
      return false;
    return true;
  }
}
