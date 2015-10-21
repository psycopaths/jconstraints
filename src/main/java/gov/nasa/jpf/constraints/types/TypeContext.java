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

package gov.nasa.jpf.constraints.types;

import java.util.HashMap;
import java.util.Map;

public class TypeContext {

  private final Map<String,Type<?>> TYPE_FOR_NAME
    = new HashMap<String,Type<?>>();
  private final Map<Class<?>,Type<?>> TYPE_FOR_CLASS
    = new HashMap<Class<?>,Type<?>>();
  
  public TypeContext() {
    this(true);
  }
  
  public TypeContext(boolean withBuiltin) {
    if(withBuiltin)
      addBuiltinTypes();
  }
  
  protected void registerType(Type<?> type) {
    String name = type.getName();
    registerType(name, type);
    String[] otherNames = type.getOtherNames();
    if(otherNames != null) {
      for(String nam : otherNames)
        registerType(nam, type);
    }
    
    Class<?> canonicalClass = type.getCanonicalClass();
    if(canonicalClass != null) {
      registerType(canonicalClass, type);
      Class<?>[] otherClasses = type.getOtherClasses();
      if(otherClasses != null) {
        for(Class<?> other : otherClasses)
          registerType(other, type);
      }
    }
  }
  
  private void registerType(String name, Type<?> type) {
    if(TYPE_FOR_NAME.get(name) == null)
      TYPE_FOR_NAME.put(name, type);
  }
  
  private void registerType(Class<?> clazz, Type<?> type) {
    if(TYPE_FOR_CLASS.get(clazz) == null)
      TYPE_FOR_CLASS.put(clazz, type);
  }
  
  
  public void addBuiltinTypes() {
    for(Type<?> t : BuiltinTypes.BUILTIN_TYPES)
      registerType(t);
  }
  
  public Type<?> byName(String name) {
    return TYPE_FOR_NAME.get(name);
  }
  
  public Type<?> byClass(Class<?> clazz) {
    return TYPE_FOR_CLASS.get(clazz);
  }
  
 
  public Type<?> mostSpecificSupertype(Type<?> typeA, Type<?> typeB) {
    if(typeA.equals(typeB))
      return typeA;
    
    TypeForest.Node a = TypeForest.findNode(typeA);
    TypeForest.Node b = TypeForest.findNode(typeB);
    
    TypeForest.Node ancestor = TypeForest.findCommonAncestor(a, b);
    
    if(ancestor == null)
      return null;
    
    return ancestor.getType();
  }
  
}
