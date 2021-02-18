/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * <p>Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p> Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com)
 * We license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.expressions;

import static gov.nasa.jpf.constraints.api.ConstraintSolver.Result.SAT;
import static gov.nasa.jpf.constraints.expressions.LogicalOperator.AND;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GE;
import static gov.nasa.jpf.constraints.expressions.NumericComparator.GT;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3Solver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.util.LinkedList;
import java.util.List;
import org.testng.annotations.Test;

public class QuantifierTest {

  @Test
  public void quantifier01Test() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "X");
    NumericBooleanExpression nbe = NumericBooleanExpression
        .create(x, GT, Constant.create(BuiltinTypes.SINT32, 5));
    List<Variable<?>> boundVar = new LinkedList<>();
    boundVar.add(x);
    QuantifierExpression qe = QuantifierExpression.create(Quantifier.FORALL, boundVar, nbe);
    NativeZ3Solver z3 = new NativeZ3Solver();
    Valuation model = new Valuation();
    ConstraintSolver.Result jRes = z3.solve(qe, model);
    assertEquals(jRes, Result.UNSAT);
    QuantifierExpression qe2 = QuantifierExpression.create(Quantifier.EXISTS, boundVar, nbe);
    jRes = z3.solve(qe2, model);
    assertEquals(jRes, SAT);
  }

  @Test
  public void quantifier04Test() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "X");
    NumericBooleanExpression nbe = NumericBooleanExpression
        .create(x, GT, Constant.create(BuiltinTypes.SINT32, 5));
    List<Variable<?>> boundVar = new LinkedList<>();
    boundVar.add(x);
    Expression qe = QuantifierExpression.create(Quantifier.FORALL, boundVar, nbe);
    qe = Negation.create(qe);
    NativeZ3Solver z3 = new NativeZ3Solver();
    Valuation model = new Valuation();
    ConstraintSolver.Result jRes = z3.solve(qe, model);
    assertEquals(jRes, SAT);
    Expression qe2 = QuantifierExpression.create(Quantifier.EXISTS, boundVar, nbe);
    qe2 = Negation.create(qe2);
    jRes = z3.solve(qe2, model);
    assertEquals(jRes, Result.UNSAT);
  }

  @Test
  public void quantifier02Test() {
    Variable x = Variable.create(BuiltinTypes.SINT32, "X");
    Variable y = Variable.create(BuiltinTypes.SINT32, "Y");
    NumericBooleanExpression nbe = NumericBooleanExpression
        .create(x, GT, Constant.create(BuiltinTypes.SINT32, 5));
    NumericBooleanExpression nbe2 = NumericBooleanExpression
        .create(y, GT, Constant.create(BuiltinTypes.SINT32, 5));
    PropositionalCompound pc = PropositionalCompound.create(nbe, AND, nbe2);
    List<Variable<?>> boundVar = new LinkedList<>();
    boundVar.add(x);
    boundVar.add(y);
    QuantifierExpression qe = QuantifierExpression.create(Quantifier.FORALL, boundVar, pc);
    NativeZ3Solver z3 = new NativeZ3Solver();
    Valuation model = new Valuation();
    ConstraintSolver.Result jRes = z3.solve(qe, model);
    assertEquals(jRes, Result.UNSAT);
  }

  @Test
  public void quantifier03Test() {
    Variable d = Variable.create(BuiltinTypes.SINT32, "D");
    Variable b = Variable.create(BuiltinTypes.BOOL, "B");
    Variable x = Variable.create(BuiltinTypes.SINT32, "X");
    Variable y = Variable.create(BuiltinTypes.SINT32, "Y");
    NumericBooleanExpression nbe = NumericBooleanExpression
        .create(x, GT, Constant.create(BuiltinTypes.SINT32, 5));
    IfThenElse ite = IfThenElse.create(b, y, d);
    NumericBooleanExpression nbe2 = NumericBooleanExpression
        .create(y, GE, ite);
    PropositionalCompound pc = PropositionalCompound.create(nbe, AND, nbe2);
    List<Variable<?>> boundVar = new LinkedList<>();
    boundVar.add(x);
    boundVar.add(y);
    QuantifierExpression qe = QuantifierExpression.create(Quantifier.FORALL, boundVar, pc);
    NativeZ3Solver z3 = new NativeZ3Solver();
    Valuation model = new Valuation();
    ConstraintSolver.Result jRes = z3.solve(qe, model);
    assertEquals(jRes, Result.UNSAT);
    Expression e = Negation.create(pc);
    jRes = z3.solve(e, model);
    assertEquals(jRes, SAT);

  }
}
