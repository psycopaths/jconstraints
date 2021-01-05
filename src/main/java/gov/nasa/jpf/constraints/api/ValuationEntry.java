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
package gov.nasa.jpf.constraints.api;

import gov.nasa.jpf.constraints.expressions.Constant;
import java.io.Serializable;
import java.util.Map;

public class ValuationEntry<E> implements Cloneable, Serializable {

  private final Variable<E> variable;
  private E value;

  public ValuationEntry(Variable<E> variable, E value) {
    this.variable = variable;
    this.value = value;
  }

  public static <E> ValuationEntry<E> create(Variable<E> variable, E value) {
    return new ValuationEntry<E>(variable, value);
  }

  public Variable<E> getVariable() {
    return variable;
  }

  public E getValue() {
    return value;
  }

  public void setValue(E value) {
    this.value = value;
  }

  @Override
  public ValuationEntry<E> clone() {
    return new ValuationEntry<E>(variable, value);
  }

  public Constant<E> valueConstant() {
    return Constant.create(variable.getType(), value);
  }

  @SuppressWarnings("rawtypes")
  public Map.Entry<Variable, Object> toEntry() {
    return new EntryWrapper();
  }

  /* (non-Javadoc)
   * @see java.lang.Object#hashCode()
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((value == null) ? 0 : value.hashCode());
    result = prime * result + ((variable == null) ? 0 : variable.hashCode());
    return result;
  }

  /* (non-Javadoc)
   * @see java.lang.Object#equals(java.lang.Object)
   */
  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    ValuationEntry<?> other = (ValuationEntry<?>) obj;
    if (value == null) {
      if (other.value != null) {
        return false;
      }
    } else if (!value.equals(other.value)) {
      return false;
    }
    if (variable == null) {
      if (other.variable != null) {
        return false;
      }
    } else if (!variable.equals(other.variable)) {
      return false;
    }
    return true;
  }

  @Deprecated
  @SuppressWarnings("rawtypes")
  private class EntryWrapper implements Map.Entry<Variable, Object>, Serializable {

    @Override
    public Variable getKey() {
      return variable;
    }

    @Override
    public Object getValue() {
      return value;
    }

    @Override
    public Object setValue(Object value) {
      throw new UnsupportedOperationException();
    }
  }
}
