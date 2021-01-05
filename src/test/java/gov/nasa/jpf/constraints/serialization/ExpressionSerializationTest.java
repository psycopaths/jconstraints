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
package gov.nasa.jpf.constraints.serialization;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.math.BigInteger;
import org.testng.annotations.Test;

public class ExpressionSerializationTest {

  @Test(groups = {"serialization", "base"})
  public void roundTripPropositionalCompoundTest() throws IOException, ClassNotFoundException {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");

    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(pc);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), pc.toString());
  }

  @Test(groups = {"serialization", "base"})
  public void runStringSerializationExample1Test() throws IOException, ClassNotFoundException {
    Variable str1 = Variable.create(BuiltinTypes.STRING, "_string0");
    Constant cInt0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0));
    Expression lessThan =
        NumericBooleanExpression.create(
            cInt0, NumericComparator.LT, StringIntegerExpression.createLength(str1));
    Negation neg = Negation.create(ExpressionUtil.and(lessThan, lessThan));
    Expression finalExpr = ExpressionUtil.and(ExpressionUtil.TRUE, neg);
    finalExpr = ExpressionUtil.and(finalExpr, ExpressionUtil.TRUE);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(finalExpr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), finalExpr.toString());
  }

  @Test(groups = {"serialization", "base"})
  public void valuationSerializationTest() throws IOException, ClassNotFoundException {
    Valuation val = new Valuation();
    Variable str1 = new Variable(BuiltinTypes.STRING, "_string1");
    val.setValue(str1, "haha");
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(val);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Valuation readVal = (Valuation) in.readObject();
    assertEquals(readVal.getValue(str1), val.getValue(str1));
  }
}
