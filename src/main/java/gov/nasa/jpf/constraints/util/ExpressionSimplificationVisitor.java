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
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;

/**
 * copies a formula
 */
final class ExpressionSimplificationVisitor extends DuplicatingVisitor<Boolean> {

  private static final ExpressionSimplificationVisitor INSTANCE = new ExpressionSimplificationVisitor(); 
  
  public static ExpressionSimplificationVisitor getInstance() {
    return INSTANCE;
  }
  
  protected ExpressionSimplificationVisitor() {
    
  }
  
  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.util.DuplicatingVisitor#defaultVisit(gov.nasa.jpf.constraints.api.Expression, java.lang.Object)
   */
  @Override
  protected <E> Expression<?> defaultVisit(Expression<E> expression,
      Boolean data) {
    Expression<?> res = super.defaultVisit(expression, data);
    return checkConstantExpression(res);
  }

  private <E> Expression<E> checkConstantExpression(Expression<E> expr) {
    Expression<?>[] children = expr.getChildren();
    
    for(int i = 0; i < children.length; i++) {
      if(!(children[i] instanceof Constant))
        return expr;
    }
    E val = expr.evaluate(null);
    return Constant.create(expr.getType(), val);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(Variable<E> v, Boolean data) {
    if(!data)
      return v;
    Expression<Boolean> asBool = v.as(BuiltinTypes.BOOL);
    if(asBool != null)
      return new Negation(asBool);
    if(v.getType() instanceof NumericType)
      return new UnaryMinus<>(v);
    throw new IllegalStateException("Cannot simplify: expression of type " + v.getType() + " is neither boolean nor numeric");
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.Constant, java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(Constant<E> c, Boolean data) {
    if(!data)
      return c;
    
    Expression<Boolean> asBool = c.as(BuiltinTypes.BOOL);
    
    if(asBool != null)
      return ExpressionUtil.boolConst(!asBool.evaluate(null));
    
    Type<E> t = c.getType();
    if(t instanceof NumericType) {
      NumericType<E> nt = (NumericType<E>)t;
      return Constant.create(nt, nt.negate(c.getValue()));
    }
    throw new IllegalStateException("Cannot simplify: expression of type " + c.getType() + " is neither boolean nor numeric");
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.Negation, java.lang.Object)
   */
  @Override
  public Expression<?> visit(Negation n, Boolean data) {
    return visit(n.getNegated(), !data);
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.NumericBooleanExpression, java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(NumericBooleanExpression n, Boolean data) {
    Expression<?> left = visit(n.getLeft(), false);
    Expression<?> right = visit(n.getRight(), false);
    
    NumericComparator effComp = n.getComparator();
    if(data)
      effComp = effComp.not();
    
    NumericBooleanExpression res = new NumericBooleanExpression(left, effComp, right);
    return checkConstantExpression(res);
  }


  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.PropositionalCompound, java.lang.Object)
   */
  @Override
  @SuppressWarnings("unchecked")
  public Expression<?> visit(PropositionalCompound n, Boolean data) {
    LogicalOperator effLop = n.getOperator();
    Boolean lneg = false, rneg = false;
    if(data) {
      switch(effLop) {
      case AND:
        effLop = LogicalOperator.OR;
        lneg = rneg = true;
        break;
      case OR:
        effLop = LogicalOperator.AND;
        lneg = rneg = true;
        break;
      case XOR:
        effLop = LogicalOperator.EQUIV;
        break;
      case EQUIV:
        effLop = LogicalOperator.XOR;
        break;
      case IMPLY:
        effLop = LogicalOperator.AND;
        rneg = true;
        break;
      }
    }
    
    Expression<Boolean> left = (Expression<Boolean>)visit(n.getLeft(), lneg);
    Expression<Boolean> right = (Expression<Boolean>)visit(n.getRight(), rneg);
    
    return new PropositionalCompound(left, effLop, right);
  }


  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.QuantifierExpression, java.lang.Object)
   */
  @Override
  @SuppressWarnings("unchecked")
  public Expression<?> visit(QuantifierExpression q, Boolean data) {
    Quantifier quant = q.getQuantifier();
    if(data)
      quant = quant.negate();
    return new QuantifierExpression(quant, q.getBoundVariables(), (Expression<Boolean>)visit(q.getBody(), data));
  }


  @SuppressWarnings("unchecked")
  public <E> Expression<E> simplify(Expression<E> e) {
    return (Expression<E>)visit(e,false);
  }
  
  

}
