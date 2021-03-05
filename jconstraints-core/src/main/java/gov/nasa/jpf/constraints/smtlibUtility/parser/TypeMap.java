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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_BOOL;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_INT;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_REAL;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_STRING;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import java.util.HashMap;

public class TypeMap {
  public static TypeMap instance;
  public HashMap<String, Type> typeMap;

  public TypeMap() {
    typeMap = new HashMap();
    initializeBasicTypes();
  }

  public void initializeBasicTypes() {
    typeMap.put(SORT_INT.toLowerCase(), BuiltinTypes.INTEGER);
    typeMap.put(SORT_BOOL.toLowerCase(), BuiltinTypes.BOOL);
    typeMap.put(SORT_REAL.toLowerCase(), BuiltinTypes.DECIMAL);
    typeMap.put(SORT_STRING.toLowerCase(), BuiltinTypes.STRING);
  }

  private static TypeMap getInstance() {
    if (instance == null) {
      instance = new TypeMap();
    }
    return instance;
  }

  public static <E> Type<E> getType(String symbol) {
    return getInstance().typeMap.get(symbol.toLowerCase());
  }
}
