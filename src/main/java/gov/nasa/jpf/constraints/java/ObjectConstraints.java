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
package gov.nasa.jpf.constraints.java;

import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.types.TypeContext;

import java.lang.reflect.Field;
import java.util.IdentityHashMap;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;

public class ObjectConstraints {
  
  private static final TypeContext javaTypes = new TypeContext(true);
  
  
  public static void addToValuation(String name, Object obj, Class<?> realClass, Valuation val) {
    if(realClass.isPrimitive()) {
      addPrimitiveToValuation(name, obj, val);
    }
    else {
      addInstanceToValuation(name, obj, Predicates.alwaysTrue(), val, new IdentityHashMap<Object,Boolean>());
    }
  }
  
  public static void addInstanceToValuation(String objName, Object obj, Predicate<? super Field> filter, Valuation val, IdentityHashMap<Object,Boolean> visited) {
    if(obj == null)
      return;
    
    if(visited.put(obj, Boolean.TRUE) != null)
      return;
    
    Field[] fields = obj.getClass().getFields();
    
    
    for(Field f : fields) {
      if(!filter.apply(f))
        continue;
      
      Class<?> ftype = f.getType();
      String fname = objName + "." + f.getName();
      
      try {
        Object value = f.get(obj);
        
        if(!ftype.isPrimitive()) {
          addInstanceToValuation(fname, value, filter, val, visited);
        }
        else {
          addPrimitiveToValuation(fname, value, val);
        }
      }
      catch(IllegalAccessException ex) {
        ex.printStackTrace();
        // IGNORE FIELD
      }
    }
  }
  
  
  public static void addPrimitiveToValuation(String name, Object value, Valuation val) {
    Variable<?> var = getPrimitiveVar(name, value.getClass());
    val.setCastedValue(var, value);
  }
  
  public static <T> Variable<T> getPrimitiveVar(String name, Class<T> clazz) {
    Type<T> t = getPrimitiveType(clazz);
    return Variable.create(t, name);
  }
  
  @SuppressWarnings("unchecked")
  public static <T> Constant<T> getPrimitiveConst(T value) {
    Type<T> t = getPrimitiveType((Class<T>)value.getClass());
    return Constant.create(t, value);
  }
  
  
  @SuppressWarnings("unchecked")
  public static <T> Type<T> getPrimitiveType(Class<T> clazz) {
    if(clazz == Boolean.class)
      return (Type<T>)BuiltinTypes.BOOL;
    if(clazz == Byte.class)
      return (Type<T>)BuiltinTypes.SINT8;
    if(clazz == Character.class)
      return (Type<T>)BuiltinTypes.UINT16;
    if(clazz == Short.class)
      return (Type<T>)BuiltinTypes.SINT16;
    if(clazz == Integer.class)
      return (Type<T>)BuiltinTypes.SINT32;
    if(clazz == Long.class)
      return (Type<T>)BuiltinTypes.SINT64;
    if(clazz == Float.class)
      return (Type<T>)BuiltinTypes.FLOAT;
    if(clazz == Double.class)
      return (Type<T>)BuiltinTypes.DOUBLE;
    throw new IllegalArgumentException("Class " + clazz.getName() + " is not a wrapper class for a primitive type");
  }
  
  public static TypeContext getJavaTypes() {
    return javaTypes;
  }
}
