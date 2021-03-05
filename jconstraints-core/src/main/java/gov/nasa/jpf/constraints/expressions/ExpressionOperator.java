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

package gov.nasa.jpf.constraints.expressions;

import java.io.Serializable;

public interface ExpressionOperator extends Serializable {
  public static ExpressionOperator fromString(String str) {
    ExpressionOperator convertedOperator = BitvectorOperator.fromString(str);
    if (convertedOperator == null) {
      convertedOperator = LogicalOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = NumericComparator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = NumericOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = StringOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = StringBooleanOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = StringIntegerOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = RegExOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = RegExCompoundOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = RegExBooleanOperator.fromString(str);
    }
    if (convertedOperator == null) {
      convertedOperator = BitvectorOperator.fromString(str);
    }
    if (convertedOperator == null) {
      throw new UnsupportedOperationException(
          "String " + str + " cannot be resolved to jConstraintsOperator");
    }
    return convertedOperator;
  }
}
