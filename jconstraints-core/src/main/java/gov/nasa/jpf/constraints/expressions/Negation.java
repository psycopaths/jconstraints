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

package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.util.Collection;

/** Logical negation */
public class Negation extends AbstractBoolExpression {

  private final Expression<Boolean> negated;

  public static Negation create(final Expression<Boolean> negated) {
    return new Negation(negated);
  }

  public Negation(final Expression<Boolean> negated) {
    this.negated = negated;
  }

  public Expression<Boolean> getNegated() {
    return this.negated;
  }

  @Override
  public Boolean evaluate(final Valuation values) {
    return !this.negated.evaluate(values);
  }

  @Override
  public Boolean evaluateSMT(Valuation values) {
    return !this.negated.evaluateSMT(values);
  }

  @Override
  public void collectFreeVariables(final Collection<? super Variable<?>> variables) {
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
  public boolean equals(final Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final Negation other = (Negation) obj;

    return negated.equals(other.negated);
  }

  @Override
  @SuppressWarnings("unchecked")
  public Expression<Boolean>[] getChildren() {
    return new Expression[] {negated};
  }

  @Override
  public Expression<Boolean> duplicate(final Expression<?>[] newChildren) {
    assert newChildren.length == 1;

    final Expression<?> newChild = newChildren[0];
    if (newChild == negated) {
      return this;
    }

    return new Negation(newChild.requireAs(BuiltinTypes.BOOL));
  }

  @Override
  public void print(final Appendable a, final int flags) throws IOException {
    a.append('!');
    negated.print(a, flags);
  }

  @Override
  public void printMalformedExpression(final Appendable a, final int flags) throws IOException {
    a.append('!');
    if (negated == null) {
      a.append("null");
    } else {
      negated.printMalformedExpression(a, flags);
    }
  }

  @Override
  public <R, D> R accept(final ExpressionVisitor<R, D> visitor, final D data) {
    return visitor.visit(this, data);
  }
}
