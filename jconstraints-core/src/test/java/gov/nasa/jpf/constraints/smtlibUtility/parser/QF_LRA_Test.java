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

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.loadResource;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;
import org.smtlib.CharSequenceReader;
import org.smtlib.IParser;
import org.testng.annotations.Test;

public class QF_LRA_Test {
  @Test(groups = {"jsmtlib", "base"})
  public void realParsingbignum_lra1Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/bignum_lra1.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(assertStmt.getClass(), PropositionalCompound.class);
    assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void realParsingCountBy2Test()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/_count_by_2.i_3_2_2.bpl_1.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(problem.getAllAssertionsAsConjunction().getClass(), PropositionalCompound.class);
    assertEquals(problem.getAllAssertionsAsConjunction().getType(), BuiltinTypes.BOOL);
    assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void realParsingIntersectionExampleTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/intersection-example.smt2");
    final Expression assertStmt = problem.assertions.get(0);
    assertEquals(problem.getAllAssertionsAsConjunction().getClass(), Negation.class);
    assertEquals(problem.getAllAssertionsAsConjunction().getType(), BuiltinTypes.BOOL);
    assertEquals(assertStmt.getType(), BuiltinTypes.BOOL);
  }

  @Test(groups = {"jsmtlib", "base"})
  public void realParsingWaterTankTest()
      throws SMTLIBParserException, IParser.ParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/water_tank-node28718.smt2");
    assertEquals(problem.getAllAssertionsAsConjunction().getClass(), Negation.class);
    assertEquals(problem.getAllAssertionsAsConjunction().getType(), BuiltinTypes.BOOL);
  }

  /*
   * For some reason, we have encountered a problem, whenever the size of the input buffer used by the
   * CharSequenceReader
   * is less than the size of the Stirng feed ot the String Builder.
   * @FIXME: Investigate further and fix in jSMTLIB interaction with JDK.
   */
  @Test(enabled = false)
  public void readingCountBy2Test() throws IOException, InterruptedException {
    final String targetResource = "test_inputs/_count_by_2.i_3_2_2.bpl_1.smt2";
    final StringBuilder b = new StringBuilder();
    final BufferedReader reader = new BufferedReader(new FileReader(loadResource(targetResource)));
    reader.lines().forEach(e -> b.append(e));

    final String fileContent = b.toString();

    System.out.println("File size: " + fileContent.length());

    final CharSequenceReader charReader = new CharSequenceReader(new StringReader(fileContent));

    final BufferedReader reader2 = new BufferedReader(new StringReader(fileContent));
    final String res = reader2.lines().reduce("", (a, e) -> a += e);

    for (int i = 0; i < fileContent.length(); i++) {
      assertEquals(
          res.charAt(i),
          fileContent.charAt(i),
          "The chars should be equals but diverged at i="
              + i
              + " got: "
              + Character.getNumericValue(res.charAt(i)));
    }

    for (int i = 0; i < fileContent.length(); i++) {
      assertEquals(
          charReader.charAt(i),
          fileContent.charAt(i),
          "The chars should be equals but diverged at i="
              + i
              + " got: "
              + Character.getNumericValue(charReader.charAt(i)));
    }
  }
}
