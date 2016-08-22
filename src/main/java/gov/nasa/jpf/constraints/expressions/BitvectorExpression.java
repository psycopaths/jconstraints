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
import gov.nasa.jpf.constraints.types.TypeContext;

import java.io.IOException;
import java.util.Collection;

public class BitvectorExpression<E>
    extends AbstractExpression<E> {
  

  public static Expression<?> createCompatible(Expression<?> left,
      BitvectorOperator op, Expression<?> right, TypeContext types) {
    Type<?> lt = left.getType(), rt = right.getType();
    Type<?> superType = types.mostSpecificSupertype(left.getType(), right.getType());
    if(!(superType instanceof BVIntegerType))
      throw new IllegalArgumentException();
    Expression<?> l = (superType.equals(lt)) ? left : CastExpression.create(left, superType);
    Expression<?> r = (superType.equals(rt)) ? right : CastExpression.create(right, superType);
    return create(l, op, r);
  }
  
  public static <E> BitvectorExpression<E> create(Expression<E> left, BitvectorOperator op, Expression<?> right) {
    BVIntegerType<E> type = (BVIntegerType<E>)left.getType();
    Expression<E> r = right.requireAs(type);
    return new BitvectorExpression<E>(left, op, r);
  }
  
  private final BitvectorOperator op;
  private final Expression<E> left;
  private final Expression<E> right;
  
  public BitvectorExpression(Expression<E> left, BitvectorOperator op, Expression<E> right) {
    this.op = op;
    this.left = left;
    this.right = right;
  }

  @Override
  public E evaluate(Valuation values) {
    E lv = left.evaluate(values);
    E rv = right.evaluate(values);
    BVIntegerType<E> type = (BVIntegerType<E>)getType();
    switch(op) {
    case AND:
      return type.and(lv, rv);
    case OR:
      return type.or(lv, rv);
    case XOR:
      return type.xor(lv, rv);
    case SHIFTL:
      return type.shiftLeft(lv, rv);
    case SHIFTR:
      return type.shiftRight(lv, rv);
    case SHIFTUR:
      return type.shiftRightUnsigned(lv, rv);
    default:
      throw new IllegalStateException("Unknown bitvector operator " + op);
    }
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    left.collectFreeVariables(variables);
    right.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  @Override
  public Type<E> getType() {
    return left.getType();
  }
  
  public BitvectorOperator getOperator() {
    return op;
  }
  
  public Expression<E> getLeft() {
    return left;
  }
  
  public Expression<E> getRight() {
    return right;
  }

  @Override
  @SuppressWarnings("unchecked")
  public Expression<E>[] getChildren() {
    return new Expression[]{left, right};
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 2;
    
    if(identical(newChildren, left, right))
      return this;
    
    return BitvectorExpression.create(newChildren[0], this.op, newChildren[1]);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(');
    left.print(a, flags);
    a.append(' ').append(op.toString()).append(' ');
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
    a.append(' ').append(op.toString()).append(' ');
    if(right == null){
      a.append("null");
    }else{
      right.printMalformedExpression(a, flags);
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
    result = prime * result + ((left == null) ? 0 : left.hashCode());
    result = prime * result + ((op == null) ? 0 : op.hashCode());
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
    BitvectorExpression<?> other = (BitvectorExpression<?>) obj;
    if (left == null) {
      if (other.left != null)
        return false;
    } else if (!left.equals(other.left))
      return false;
    if (op != other.op)
      return false;
    if (right == null) {
      if (other.right != null)
        return false;
    } else if (!right.equals(other.right))
      return false;
    return true;
  }

  

}
