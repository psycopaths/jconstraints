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
package gov.nasa.jpf.constraints.types;

import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;

public class NamedSort implements Type<Void> {

  private String name;

  public NamedSort(String name) {
    this.name = name;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public String[] getOtherNames() {
    return new String[0];
  }

  @Override
  public Class<Void> getCanonicalClass() {
    return null;
  }

  @Override
  public Class<?>[] getOtherClasses() {
    return new Class[0];
  }

  @Override
  public Void cast(Object other) {
    return null;
  }

  @Override
  public Void getDefaultValue() {
    return null;
  }

  @Override
  public Type<?> getSuperType() {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Void> cast(Type<O> fromType) {
    return null;
  }

  @Override
  public <O> CastOperation<? super O, ? extends Void> requireCast(Type<O> fromType) {
    return null;
  }

  @Override
  public Void parse(String string) throws ImpreciseRepresentationException {
    return null;
  }
}
