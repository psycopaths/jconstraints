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

public interface Type<T> {

  public String getName();
  
  public String[] getOtherNames();
  
  public Class<T> getCanonicalClass();

  public Class<?>[] getOtherClasses();

  public T cast(Object other);

  public T getDefaultValue();

  public Type<?> getSuperType();

  public <O> CastOperation<? super O,? extends T> cast(Type<O> fromType);
  public <O> CastOperation<? super O,? extends T> requireCast(Type<O> fromType);

  public abstract T parse(String string);

  
	
}
