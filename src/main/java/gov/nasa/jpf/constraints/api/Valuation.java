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

import gov.nasa.jpf.constraints.util.AbstractPrintable;

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Function;

/**
 * valuation of a number of variables (identified by names).
 */
public class Valuation extends AbstractPrintable implements Iterable<ValuationEntry<?>>, Function<Variable<?>,Expression<?>> {
  
  private Map<Variable<?>,ValuationEntry<?>> entries = new HashMap<Variable<?>,ValuationEntry<?>>();
  
  
  @SuppressWarnings("unchecked")
  public <E> ValuationEntry<E> getEntry(Variable<E> var) {
    return (ValuationEntry<E>)entries.get(var);
  }
  
  public <E> E getValue(Variable<E> var) {
    ValuationEntry<E> entry = getEntry(var);
    if(entry == null)
      return var.getType().getDefaultValue();
    return entry.getValue();
  }

  public <E> void setValue(Variable<E> var, E value) {
    ValuationEntry<E> entry = getEntry(var);
    if(entry != null) {
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
    return this.entries.containsKey(v);
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
    
    for(ValuationEntry<?> e : entries.values()) {
      if(first)
        first = false;
      else
        a.append(',');
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

  public <E> void setParsedValue(Variable<E> v, String strVal) {
    setValue(v, v.getType().parse(strVal));
  }

  public <E> void addEntry(ValuationEntry<E> e) {
    setValue(e.getVariable(), e.getValue());
  }

  public void putAll(Valuation v) {
    putAll(v, true);
  }
  
  public void putAll(Valuation v, boolean override) {
    for(Map.Entry<Variable<?>,ValuationEntry<?>> e : v.entries.entrySet()) {
      Variable<?> var = e.getKey();
      if(override || !entries.containsKey(e.getKey()))
        entries.put(var, e.getValue().clone());
    }
  }
  
  @Override
  public Expression<?> apply(Variable<?> var) {
    ValuationEntry<?> e = entries.get(var);
    if(e == null)
      return var;
    return e.valueConstant();
  }

  public Object getValue(String varName) {
    for(ValuationEntry<?> e : entries.values()) {
      if(e.getVariable().getName().equals(varName))
        return e.getValue();
    }
    return null;
  }
     
  
  @Deprecated
  @SuppressWarnings("rawtypes")
  public Set<Map.Entry<Variable,Object>> entrySet() {
    Set<Map.Entry<Variable,Object>> entries = new HashSet<>();
    for(ValuationEntry<?> e : this.entries.values()) {
      entries.add(e.toEntry());
    }
    return entries;
  }
}
