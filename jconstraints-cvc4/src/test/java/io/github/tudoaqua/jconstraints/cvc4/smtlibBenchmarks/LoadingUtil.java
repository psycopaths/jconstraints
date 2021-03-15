/*
 * Copyright 2017-2021 The jConstraints-cvc4 Authors
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

package io.github.tudoaqua.jconstraints.cvc4.smtlibBenchmarks;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class LoadingUtil {

  public static SMTProblem loadProblemFromResources(String name)
      throws URISyntaxException, IOException, SMTLIBParserException {
    URL smtFile = QF_LIA_RoundTripTest.class.getClassLoader().getResource(name);
    List<String> input = Files.readAllLines(Paths.get(smtFile.toURI()));
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            input.stream()
                .reduce(
                    "",
                    (a, b) -> {
                      return b.startsWith(";") ? a : a + b;
                    }));
    return problem;
  }
}
