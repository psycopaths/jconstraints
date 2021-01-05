/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.simplifiers;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashSet;
import java.util.Set;
import org.testng.annotations.BeforeClass;
import org.testng.annotations.Test;

public class ExpressionTailoringUtilTest {
  Variable x = Variable.create(BuiltinTypes.SINT32, "x");
  Variable j = Variable.create(BuiltinTypes.SINT32, "j");
  Variable i = Variable.create(BuiltinTypes.SINT32, "i");

  Constant c1 = Constant.create(BuiltinTypes.SINT32, 10);
  Constant c2 = Constant.create(BuiltinTypes.SINT32, 5);

  Expression assignentIJ =
      NumericBooleanExpression.create(
          j, NumericComparator.EQ, NumericCompound.create(i, NumericOperator.PLUS, c2));

  Expression constraintI = NumericBooleanExpression.create(i, NumericComparator.LT, c2);
  Expression constraintJ = NumericBooleanExpression.create(j, NumericComparator.LT, c1);

  Expression assignmentXJ = NumericBooleanExpression.create(x, NumericComparator.EQ, j);

  Set<Variable<?>> vars;

  @BeforeClass(alwaysRun = true)
  public void setUp() {
    vars = new HashSet<>();
    vars.add(x);
  }

  @Test(groups = {"simplifiers", "base"})
  public void disjunctClausesTest() {
    Expression testInput = ExpressionUtil.and(constraintJ, x);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), x);
  }

  @Test(groups = {"simplifiers", "base"})
  public void directJoinedTest() {
    Expression testInput = ExpressionUtil.and(assignmentXJ, constraintJ, constraintI);
    Expression expected = ExpressionUtil.and(assignmentXJ, constraintJ);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
  }

  @Test(groups = {"simplifiers", "base"})
  public void chainedWithOverlayTest() {
    Expression testInput = ExpressionUtil.and(assignentIJ, constraintI, constraintJ, assignmentXJ);
    Expression expected = ExpressionUtil.and(assignmentXJ, assignentIJ, constraintI, constraintJ);
    assertEquals(ExpressionTailoringUtil.tailor(testInput, vars), expected);
  }

  @Test(groups = {"simplifiers", "base"})
  public void debuggingWhileLoopTest() {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");
    Variable c = Variable.create(BuiltinTypes.BOOL, "c");
    Expression part1 = ExpressionUtil.and(new Negation(a), new Negation(b));
    Expression part2 = ExpressionUtil.and(c, new Negation(part1));
    Valuation init = new Valuation();
    init.addEntry(new ValuationEntry<>(a, true));
    init.addEntry(new ValuationEntry<>(b, false));
    assertEquals(ExpressionTailoringUtil.tailor(part2, init.getVariables()), new Negation(part1));
  }
}
