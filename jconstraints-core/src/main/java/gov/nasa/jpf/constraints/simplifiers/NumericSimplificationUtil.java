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

package gov.nasa.jpf.constraints.simplifiers;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.simplifiers.datastructures.ArithmeticVarReplacements;
import gov.nasa.jpf.constraints.simplifiers.datastructures.AssignmentCollector;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.List;

public class NumericSimplificationUtil {

  public static Expression simplify(Expression<?> e) {
    AssignmentCollector collector = new AssignmentCollector();
    CollectAssignmentVisitor visitor = new CollectAssignmentVisitor();
    e.accept(visitor, collector);
    ArithmeticVarReplacements replacements = collector.convertToArithmeticVarReplacements();
    List<Expression> toPrune = collector.getToPrune();

    ExpressionPruningVisitor pruner = new ExpressionPruningVisitor();
    Expression<?> pruned = e.accept(pruner, toPrune);

    Expression replacedExpression = ExpressionUtil.transformVars(pruned, replacements);
    return replacedExpression;
  }
}
