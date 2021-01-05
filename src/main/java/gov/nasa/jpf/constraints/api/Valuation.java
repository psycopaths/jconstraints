/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377
 * the original license is:
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
 *
 * Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues
 * under Apache 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.api;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.exceptions.EvaluationException;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.util.AbstractPrintable;
import java.io.IOException;
import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/** valuation of a number of variables (identified by names). */
public class Valuation extends AbstractPrintable
    implements Iterable<ValuationEntry<?>>, Function<Variable<?>, Expression<?>>, Serializable {

  private Map<Variable<?>, ValuationEntry<?>> entries =
      new HashMap<Variable<?>, ValuationEntry<?>>();

  @SuppressWarnings("unchecked")
  public <E> ValuationEntry<E> getEntry(Variable<E> var) {
    return (ValuationEntry<E>) entries.get(var);
  }

  public <E> E getValue(Variable<E> var) {
    ValuationEntry<E> entry = getEntry(var);
    if (entry == null) {
      for (ValuationEntry e : entries.values()) {
        Variable entryVar = e.getVariable();
        if (entryVar.getName().equals(var.getName()) && entryVar.getType().equals(var.getType())) {
          return (E) e.getValue();
        }
      }
      throw new EvaluationException("Valuation has no value for: " + var.getName());
    }
    return entry.getValue();
  }

  public <E> void setValue(Variable<E> var, E value) {
    ValuationEntry<E> entry = getEntry(var);
    if (entry != null) {
      entry.setValue(value);
      return;
    }
    entry = ValuationEntry.create(var, value);
    entries.put(var, entry);
  }

  public <E> void setCastedValue(Variable<E> var, Object value) {
    setValue(var, var.getType().cast(value));
  }

  public boolean containsValueFor(Variable<?> v) {
    boolean isEntry = this.entries.containsKey(v);
    if (!isEntry) {
      for (Variable key : this.entries.keySet()) {
        if (v.getName().equals(key.getName()) && v.getType().equals(key.getType())) {
          isEntry = true;
          break;
        }
      }
    }
    return isEntry;
  }

  public Set<Variable<?>> getVariables() {
    return this.entries.keySet();
  }

  public Collection<ValuationEntry<?>> entries() {
    return Collections.unmodifiableCollection(entries.values());
  }

  @Override
  public int hashCode() {
    return entries.hashCode();
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final Valuation other = (Valuation) obj;

    return this.entries.equals(other.entries);
  }

  @Override
  public void print(Appendable a) throws IOException {
    boolean first = true;
    for (ValuationEntry<?> e : entries.values()) {
      if (first) {
        first = false;
      } else {
        a.append(',');
      }
      a.append(e.getVariable().getName()).append(":=").append(String.valueOf(e.getValue()));
    }
  }

  @Override
  public Iterator<ValuationEntry<?>> iterator() {
    return Collections.unmodifiableCollection(entries.values()).iterator();
  }

  public <E> void setDefaultValue(Variable<E> r) {
    setValue(r, r.getType().getDefaultValue());
  }

  public <E> void setParsedValue(Variable<E> v, String strVal)
      throws ImpreciseRepresentationException {
    setValue(v, v.getType().parse(strVal));
  }

  public <E> void setUnsafeParsedValue(Variable<E> v, String strVal)
      throws ImpreciseRepresentationException {
    setValue(v, v.getType().parseUnsafe(strVal));
  }

  public <E> void addEntry(ValuationEntry<E> e) {
    setValue(e.getVariable(), e.getValue());
  }

  public void putAll(Valuation v) {
    putAll(v, true);
  }

  public void putAll(Valuation v, boolean override) {
    for (Map.Entry<Variable<?>, ValuationEntry<?>> e : v.entries.entrySet()) {
      Variable<?> var = e.getKey();
      if (override || !entries.containsKey(e.getKey())) {
        entries.put(var, e.getValue().clone());
      }
    }
  }

  @Override
  public Expression<?> apply(Variable<?> var) {
    ValuationEntry<?> e = entries.get(var);
    if (e == null) {
      return var;
    }
    return e.valueConstant();
  }

  public Object getValue(String varName) {
    for (ValuationEntry<?> e : entries.values()) {
      if (e.getVariable().getName().equals(varName)) {
        return e.getValue();
      }
    }
    return null;
  }

  @Deprecated
  @SuppressWarnings("rawtypes")
  public Set<Map.Entry<Variable, Object>> entrySet() {
    Set<Map.Entry<Variable, Object>> entries = new HashSet<>();
    for (ValuationEntry<?> e : this.entries.values()) {
      entries.add(e.toEntry());
    }
    return entries;
  }
}
