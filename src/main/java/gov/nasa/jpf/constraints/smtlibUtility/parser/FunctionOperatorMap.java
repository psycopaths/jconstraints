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
package gov.nasa.jpf.constraints.smtlibUtility.parser;

import java.util.HashMap;

/**
 * The same function operators are slightly named differently in jConstraints and SMT-LIB due to
 * historic reasons. While jConstraints use function operators closer to programming languages
 * SMT-LIB uses them in the mathematical sense. @Author Malte Mues
 */
public class FunctionOperatorMap {
  public static FunctionOperatorMap instance;
  public HashMap<String, String> typeMap;

  public FunctionOperatorMap() {
    typeMap = new HashMap();
    initializeBasicTypes();
  }

  public void initializeBasicTypes() {
    typeMap.put("=", "==");
    typeMap.put("and", "&&");
    typeMap.put("or", "||");
    typeMap.put("div", "/");
  }

  private static FunctionOperatorMap getInstance() {
    if (instance == null) {
      instance = new FunctionOperatorMap();
    }
    return instance;
  }

  public static String getjConstraintOperatorName(String symbol) {
    return getInstance().typeMap.getOrDefault(symbol.toLowerCase(), symbol);
  }
}
