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

package gov.nasa.jpf.constraints.api;

import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;

public interface ExpressionVisitor<R, D> {

  public <E> R visit(Variable<E> v, D data);

  public <E> R visit(Constant<E> c, D data);

  public R visit(Negation n, D data);

  public <E> R visit(NumericBooleanExpression n, D data);

  public <F, E> R visit(
      CastExpression<F, E> cast, D data);

  public <E> R visit(NumericCompound<E> n, D data);

  public R visit(PropositionalCompound n, D data);

  public <E> R visit(IfThenElse<E> n, D data);
  
  public <E> R visit(
      UnaryMinus<E> n, D data);
  
  public <E> R visit(
      BitvectorExpression<E> bv, D data);
  
  public <E> R visit(
      BitvectorNegation<E> n, D data);

  public R visit(QuantifierExpression q, D data);
  
  public <E> R visit(FunctionExpression<E> f, D data);

}