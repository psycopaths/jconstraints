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

package gov.nasa.jpf.constraints.smtlib;

import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;

public class LoadingUtil {

  public static SMTProblem loadProblemFromResources(Path name)
      throws SMTLIBParserException, IOException, URISyntaxException {
    return loadProblemFromResources(name.toString());
  }

  public static SMTProblem loadProblemFromResources(String name)
      throws URISyntaxException, IOException, SMTLIBParserException {
    URL smtFile = LoadingUtil.class.getClassLoader().getResource(name);
    File fileFromURI = new File(smtFile.toURI());
    SMTProblem problem = SMTLIBParser.parseSMTProgramFromFile(fileFromURI.getAbsolutePath());
    return problem;
  }
}
