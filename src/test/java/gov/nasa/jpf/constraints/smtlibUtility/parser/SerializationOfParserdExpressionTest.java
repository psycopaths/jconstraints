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

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class SerializationOfParserdExpressionTest {

  @Test(groups = {"jsmtlib", "base"})
  public void parsing17133_indexofTest()
      throws SMTLIBParserException, IParser.ParserException, IOException, ClassNotFoundException {
    final SMTProblem problem = parseResourceFile("17133_indexof-008.smt2");
    Expression expr = problem.getAllAssertionsAsConjunction();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(expr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    NumericBooleanExpression readVal = (NumericBooleanExpression) in.readObject();
    assertEquals(readVal.getClass(), NumericBooleanExpression.class);
    StringIntegerExpression right = (StringIntegerExpression) (readVal).getRight();
    assertEquals(right.getChildren().length, 3);
  }
}
