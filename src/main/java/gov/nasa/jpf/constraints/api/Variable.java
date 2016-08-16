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

import gov.nasa.jpf.constraints.java.ObjectConstraints;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Collection;

/**
 * named variable
 */
public class Variable<E> extends Expression<E> {

  public static <E> Variable<E> create(Type<E> type, String name) {
    return new Variable<E>(type, name);
  }
  
  public static <E> Variable<E> createAnonymous(Type<E> type) {
    return new Variable<E>(type);
  }
  
  private final Type<E> type;
  
  private final String name;

  
  public Variable(Type<E> type) {
    this(type, null);
  }
  
  public Variable(Type<E> type, String name) {
    this.type = type;
    this.name = name;
  }

  @Override
  public E evaluate(Valuation values) {
    return values.getValue(this);
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    variables.add(this);
  }
  
  @Override
  public boolean equals(Object obj) {
    if(obj == this) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    // Special case: Anonymous variables are only equal to their INSTANCE
    if(name == null) {
      return false;
    }
    
    if(obj.getClass() != Variable.class) {
      return false;
    }
    final Variable<?> other = (Variable<?>) obj;
    
    if(!this.type.equals(other.type))
      return false;
    
    return this.name.equals(other.name);
  }

  @Override
  public int hashCode() {
    if(name == null) // Identity-based equals/hashCode semantics for anonymous variables
      return super.hashCode(); 
    
    int hash = 7;
    hash = 47 * hash + (this.type != null ? this.type.hashCode() : 0);
    hash = 47 * hash + (this.name != null ? this.name.hashCode() : 0);
    return hash;
  }

  
  public String getName() {
    return this.name;
  }

  @Override
  public Expression<?>[] getChildren() {
    return NO_CHILDREN;
  }

  @Override
  public Expression<E> duplicate(Expression<?>[] newChildren) {
    assert newChildren.length == 0;
    return this;
  }

  @Override
  public Type<E> getType() {
    return type;
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    boolean qid = quoteIdentifiers(flags);
    if(qid)
      a.append('\'');
    a.append(name);
    if(qid)
      a.append('\'');
    if(includeVariableType(flags)) {
      a.append(':');
      a.append(type.getName());
    }
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags)
          throws IOException{
    boolean qid = quoteIdentifiers(flags);
    if(qid)
      a.append('\'');
    if(name == null){
      a.append("null");
    }else {
      a.append(name);
    }
    if(qid)
      a.append('\'');
    if(includeVariableType(flags)) {
      a.append(':');
      if(type == null){
        a.append("null");
      } else {
        a.append(type.getName());
      }
    }
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

  public void printTyped(Appendable a) throws IOException {
    print(a, DEFAULT_FLAGS | INCLUDE_VARIABLE_TYPE);
  }
  
  
  
  
  
  // LEGACY API
  
  @Deprecated
  public Variable(Class<E> clazz, String name) {
    this(ObjectConstraints.getPrimitiveType(clazz), name);
  }
  
}
