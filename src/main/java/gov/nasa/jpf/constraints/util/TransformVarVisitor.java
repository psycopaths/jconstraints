/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.util;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;

class TransformVarVisitor
    extends DuplicatingVisitor<Function<? super Variable<?>, ? extends Expression<?>>> {

  private static final TransformVarVisitor INSTANCE = new TransformVarVisitor();

  public static TransformVarVisitor getInstance() {
    return INSTANCE;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, java.lang.Object)
   */
  @Override
  public <E> Expression<?> visit(
      Variable<E> v, Function<? super Variable<?>, ? extends Expression<?>> data) {
    return data.apply(v);
  }

  public <T> Expression<T> apply(
      Expression<T> expr, Function<? super Variable<?>, ? extends Expression<?>> transform) {
    return visit(expr, transform).requireAs(expr.getType());
  }
}
