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


public interface BVIntegerType<T> extends IntegerType<T> {

  public int getNumBits();
  
  public T shiftLeft(T value, T shiftAmt);
  public T shiftRight(T value, T shiftAmt);
  public T shiftRightUnsigned(T value, T shiftAmt);
  
  public T not(T value);
  public T and(T left, T right);
  public T or(T left, T right);
  public T xor(T left, T right);
}
