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

import gov.nasa.jpf.constraints.casts.CastOperation;

public abstract class ConcreteType<T> implements Type<T> {

  private final String name;
  private final Type<?> superType;
  private final T defaultValue;
  
  private final Class<T> canonicalClass;
  private final Class<?>[] otherClasses;
  
  private final String[] otherNames;
  
  
  public ConcreteType(String name, Class<T> canonicalClass, T defaultValue, Type<?> superType, String[] otherNames, Class<?> ...otherClasses) {
    this.name = name;
    this.superType = superType;
    this.defaultValue = defaultValue;
    this.canonicalClass = canonicalClass;
    this.otherClasses = otherClasses;
    this.otherNames = otherNames;
  }

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.types.Type#getName()
   */
  @Override
  public String getName() {
    return name;
  }
  
  @Override
  public String[] getOtherNames() {
    return otherNames.clone(); // defensive copy
  }


  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.types.Type#getCanonicalClass()
   */
  @Override
  public Class<T> getCanonicalClass() {
    return canonicalClass;
  }


  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.types.Type#getOtherClasses()
   */
  @Override
  public Class<?>[] getOtherClasses() {
    return otherClasses.clone(); // defensive copy
  }




  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.types.Type#getDefaultValue()
   */
  @Override
  public T getDefaultValue() {
    return defaultValue;
  }


  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.types.Type#getSuperType()
   */
  @Override
  public Type<?> getSuperType() {
    return superType;
  }


  @Override
  public <O> CastOperation<? super O, ? extends T> cast(Type<O> fromType) {
    if(fromType instanceof ConcreteType) {
      ConcreteType<O> ctype = (ConcreteType<O>)fromType;
      CastOperation<? super O, ? extends T> castOp = castFrom(ctype);
      if(castOp == null)
        castOp = ctype.castTo(this);
      return castOp;
    }
    return null;
  }


  @Override
  public <O> CastOperation<? super O, ? extends T> requireCast(Type<O> fromType) {
    CastOperation<? super O,? extends T> op = cast(fromType);
    if(op == null)
      throw new IllegalArgumentException("Required cast from type " + fromType + ", but none declared");
    return op;
  }



  protected <O> CastOperation<? super T,? extends O> castTo(Type<O> toType) {
    return null;
  }
  
  protected <O> CastOperation<? super O,? extends T> castFrom(Type<O> fromType) {
    return null;
  }
}
