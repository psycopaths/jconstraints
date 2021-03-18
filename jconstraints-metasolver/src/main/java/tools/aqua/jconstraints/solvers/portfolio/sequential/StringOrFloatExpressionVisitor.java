/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>The JConstraints Meta-Solver is licensed under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tools.aqua.jconstraints.solvers.portfolio.sequential;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class StringOrFloatExpressionVisitor extends AbstractExpressionVisitor<Boolean, Void> {

  @Override
  public <E> Boolean visit(Variable<E> v, Void data) {
    return v.getType().equals(BuiltinTypes.STRING)
        || v.getType().equals(BuiltinTypes.FLOAT)
        || v.getType().equals(BuiltinTypes.DOUBLE);
  }

  @Override
  public <E> Boolean visit(Constant<E> c, Void data) {
    return c.getType().equals(BuiltinTypes.STRING)
        || c.getType().equals(BuiltinTypes.FLOAT)
        || c.getType().equals(BuiltinTypes.DOUBLE);
  }

  @Override
  public <F, E> Boolean visit(CastExpression<F, E> cast, Void data) {
    return true;
  }

  @Override
  protected <E> Boolean defaultVisit(Expression<E> expression, Void data) {
    boolean res = false;
    for (Expression child : expression.getChildren()) {
      res = res || visit(child);
    }
    return res;
  }
}
