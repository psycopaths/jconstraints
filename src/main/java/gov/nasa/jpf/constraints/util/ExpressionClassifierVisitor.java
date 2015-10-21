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
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionClassifierVisitor.ExpressionType;

class ExpressionClassifierVisitor extends AbstractExpressionVisitor<ExpressionType, Void> {

  public static enum ExpressionType { CONSTANT, LINEAR, NONLINEAR }
  private final static ExpressionType CONSTANT = ExpressionType.CONSTANT;
  private final static ExpressionType LINEAR = ExpressionType.LINEAR;
  private final static ExpressionType NONLINEAR = ExpressionType.NONLINEAR;
  
  private static final ExpressionClassifierVisitor INSTANCE = new ExpressionClassifierVisitor();
  
  public static ExpressionClassifierVisitor getInstance() {
    return INSTANCE;
  }
  
  protected ExpressionClassifierVisitor() {}
  
  
  public <E> ExpressionType getExpressionType(Expression<E> expr) {
    return this.visit(expr);
  }
  
  @Override
  public <E> ExpressionType visit(NumericCompound<E> n, Void data) {
    ExpressionType lt = visit(n.getLeft());
    ExpressionType rt = visit(n.getRight());
    
    switch (n.getOperator()) {
    case PLUS:
    case MINUS:
      if(lt == NONLINEAR || rt == NONLINEAR)
        return NONLINEAR;
      else if(lt == CONSTANT && rt == CONSTANT)
        return CONSTANT;
      else
        return LINEAR;
    case MUL:
    case DIV: //this could be made more succinct..
      if (lt == CONSTANT && rt == CONSTANT)
        return CONSTANT;
      else if(lt == NONLINEAR || rt == NONLINEAR)
        return NONLINEAR;
      else if(lt == LINEAR && rt == LINEAR)
        return NONLINEAR;
      else //must involve a linear constraint AND a constant i.e. they are linear
        return LINEAR;
    case REM:
    default:
      throw new UnsupportedOperationException(n.getOperator() + " not supported (yet)");
    }
  }
  
  @Override
  public <E> ExpressionType visit(Constant<E> c, Void data) {
    return CONSTANT;
  }
  
  @Override
  public <E> ExpressionType visit(Variable<E> v, Void data) {
    return LINEAR;
  }
  
  
  @Override
  public <F, E> ExpressionType visit(CastExpression<F,E> cast, Void data) {
    return visit(cast.getCasted());
  }
  
  @Override
  public ExpressionType visit(Negation n, Void data) {
    return visit(n.getNegated());
  }
  
  //This is an important one: if the argument to a library method is linear or nonlinear, we
  //regard the expression as nonlinear
  @Override
  public <E> ExpressionType visit(gov.nasa.jpf.constraints.expressions.functions.FunctionExpression<E> f, Void data) {
  //  if(f.getType() instanceof BuiltinTypes.BoolType)
   //   return LINEAR;
    for(Expression<?> a : f.getArgs()) {
      if(visit(a) == NONLINEAR || visit(a) == LINEAR)
        return NONLINEAR;
    }
    //We assume methods without side effects
    return CONSTANT;
  }
  
  @Override
  public <E> ExpressionType visit(UnaryMinus<E> n, Void data) {
    return visit(n.getNegated());
  }
  
  @Override
  public ExpressionType visit(PropositionalCompound n, Void data) {
    ExpressionType lt = visit(n.getLeft());
    ExpressionType rt = visit(n.getRight());
    
    if(lt == NONLINEAR || rt == NONLINEAR)
      return NONLINEAR;
    if(lt == LINEAR || rt == LINEAR)
      return LINEAR;
    else 
      return CONSTANT;
  }
  
  @Override
  public <E> ExpressionType visit(NumericBooleanExpression n, Void data) {
    ExpressionType lt = visit(n.getLeft());
    ExpressionType rt = visit(n.getRight());
    
    if(lt == NONLINEAR || rt == NONLINEAR)
      return NONLINEAR;
    if(lt == LINEAR || rt == LINEAR)
      return LINEAR;
    else 
      return CONSTANT;
  }
}
