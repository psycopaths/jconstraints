/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.simplifiers.datastructures;

import com.google.common.base.Function;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import java.util.HashMap;
import java.util.Map;

public class ArithmeticVarReplacements implements Function<Variable<?>, Expression<?>> {

  private Map<Variable, Expression> replacements;

  public ArithmeticVarReplacements(Map<Variable, Expression> replacements) {
    this.replacements = new HashMap(replacements);
  }

  public void putAll(Map<Variable, Expression> addition) {
    replacements.putAll(addition);
  }

  @Override
  public Expression apply(Variable variable) {
    return replacements.getOrDefault(variable, variable);
  }

  @Override
  public boolean equals(Object o) {
    throw new UnsupportedOperationException("This function has no Equivalence");
  }
}
