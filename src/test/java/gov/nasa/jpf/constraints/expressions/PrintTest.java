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
/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.expressions;

import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import org.testng.annotations.BeforeTest;
import org.testng.annotations.Test;

@Test
public class PrintTest {

  Expression exprUnderTest;

  @BeforeTest(alwaysRun = true)
  public void setupExpression() {
    Variable var1 = Variable.create(BuiltinTypes.SINT32, "X");
    Variable var2 = Variable.create(BuiltinTypes.SINT32, "Y");
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 5);
    Constant c2 = Constant.create(BuiltinTypes.SINT32, 8);

    NumericCompound compound1 = new NumericCompound(var1, NumericOperator.PLUS, c1);
    NumericCompound compound2 = new NumericCompound(var1, NumericOperator.MINUS, c2);
    NumericBooleanExpression bool1 = new NumericBooleanExpression(var2, NumericComparator.EQ, null);
    NumericBooleanExpression bool2 = new NumericBooleanExpression(null, NumericComparator.EQ, c2);
    PropositionalCompound compound3 = new PropositionalCompound(bool1, LogicalOperator.OR, bool2);
    exprUnderTest = compound3;
  }

  @Test(groups = {"expressions", "base"})
  public void testMalformedPrint() {
    StringBuilder builder = new StringBuilder();
    try {
      exprUnderTest.printMalformedExpression(builder);
    } catch (IOException ex) {
    }
    String result = builder.toString();
    assertTrue(result.contains("null"));
  }

  @Test(
      expectedExceptions = {NullPointerException.class},
      groups = {"expressions", "base"})
  public void testPrint() {
    StringBuilder builder = new StringBuilder();
    try {
      exprUnderTest.print(builder);
    } catch (IOException e) {
    }
  }
}
