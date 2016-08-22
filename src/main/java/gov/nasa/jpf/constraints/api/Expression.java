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

import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.AbstractPrintable;

import java.io.IOException;
import java.util.Collection;
import java.util.Map;
import java.util.Set;



/**
 * Expressions consist of terms, and can be evaluated E
 */
public abstract class Expression<E> extends AbstractPrintable {
  
  
  public static final int QUOTE_IDENTIFIERS = 1;
  public static final int INCLUDE_VARIABLE_TYPE = 2;
  public static final int INCLUDE_BOUND_DECL_TYPE = 4;
  public static final int SIMPLE_PROP_OPERATORS = 8;
  
  public static final int DEFAULT_FLAGS = QUOTE_IDENTIFIERS | INCLUDE_BOUND_DECL_TYPE;
  
  public static final int JAVA_COMPAT_FLAGS = SIMPLE_PROP_OPERATORS;
  
  public static boolean quoteIdentifiers(int printFlags) {
    return (printFlags & QUOTE_IDENTIFIERS) == QUOTE_IDENTIFIERS;
  }
  
  public static boolean includeVariableType(int printFlags) {
    return (printFlags & INCLUDE_VARIABLE_TYPE) == INCLUDE_VARIABLE_TYPE;
  }
  
  public static boolean includeBoundDeclType(int printFlags) {
    return (printFlags & INCLUDE_BOUND_DECL_TYPE) == INCLUDE_BOUND_DECL_TYPE;
  }
  
  public static Expression<?>[] NO_CHILDREN = new Expression[0];
  
    
  /**
   * evaluates using the provided values for symbolic variables
   * 
   * @param values
   * @return 
   */
  public abstract E evaluate(Valuation values);  
  
  /**
   * collect all symbolic variables
   * 
   * @param names 
   */
  public abstract void collectFreeVariables(Collection<? super Variable<?>> variables);
  
  public abstract <R,D> R accept(ExpressionVisitor<R, D> visitor, D data);
  
  
  public abstract Type<E> getType();
  
  public Class<E> getResultType() {
    return getType().getCanonicalClass();
  }
  
  
  public abstract Expression<?>[] getChildren();
  public abstract Expression<?> duplicate(Expression<?>[] newChildren);
  
  @SuppressWarnings("unchecked")
  public <F> Expression<F> as(Type<F> type) {
    Type<E> thisType = getType();
    if(!thisType.equals(type))
      return null;
    return (Expression<F>)this;
  }
  
  public <F> Expression<F> requireAs(Type<F> type) {
    Expression<F> exp = as(type);
    if(exp == null)
      throw new IllegalArgumentException("Expected type " + type + ", is " + getType());
    return exp;
  }
  
  public abstract void print(Appendable a, int flags) throws IOException;

  /**A malformed Expression might contain a null value.
  This method should only be used in debug environment
   * @throws java.io.IOExceptions*/
  public abstract void printMalformedExpression(Appendable a, int flags)
          throws IOException;

  public String toString(int flags) {
    StringBuilder sb = new StringBuilder();
    try {
      print(sb, flags);
      return sb.toString();
    }
    catch(IOException ex) {
      throw new RuntimeException("Unexpected IOException writing to StringBuilder");
    }
  }
  
  @Override
  public final void print(Appendable a) throws IOException {
    print(a, DEFAULT_FLAGS);
  }
  
  public final void printMalformedExpression(Appendable a) throws IOException {
    printMalformedExpression(a, DEFAULT_FLAGS);
  }

  
  // LEGACY API
  
  /**
   * replace terms according to replace
   * 
   * @param replace
   * @return 
   */
  @Deprecated
  @SuppressWarnings("rawtypes")
  public Expression replaceTerms(Map<Expression,Expression> replacements) {
    Expression<?> rep = replacements.get(this);
    if(rep != null)
      return rep;
    Expression<?>[] children = getChildren();
    
    boolean changed = false;
    for(int i = 0; i < children.length; i++) {
      Expression<?> old = children[i];
      Expression<?> newExp = old.replaceTerms(replacements);
      if(old != newExp)
        changed = true;
      children[i] = newExp;
    }
    
    if(!changed)
      return this;
    
    return duplicate(children);
  }
  
  @Deprecated
  @SuppressWarnings("rawtypes")
  public void getVariables(Set<Variable> variables) {
    collectFreeVariables(variables);
  }
  
}
