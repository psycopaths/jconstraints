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
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import java.io.IOException;
import java.util.Collection;

/**
 * This class should be implemented since equality is a more general concept than numeric comparison
 * (e.g., applies to boolean values also).
 */
public class EqualityExpression extends AbstractBoolExpression {

  @Override
  public Boolean evaluate(Valuation values) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    // TODO Auto-generated method stub

  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression<?>[] getChildren() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    // TODO Auto-generated method stub
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    // TODO Auto-generated method stub
  }
}
