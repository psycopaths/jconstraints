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

package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.Properties;

public class SMTLibExportSolverProvider implements ConstraintSolverProvider {

  @Override
  public String[] getNames() {
    return new String[] {SMTLibExportWrapper.NAME};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    String backName = config.getProperty(SMTLibExportWrapper.NAME + ".back");
    String resultFile = config.getProperty(SMTLibExportWrapper.NAME + ".resultFile", null);
    String singleQueryFolder =
        config.getProperty(SMTLibExportWrapper.NAME + ".singleQueryFolder", null);
    ConstraintSolverFactory f = new ConstraintSolverFactory();
    ConstraintSolver back = f.createSolver(backName);
    PrintStream out = System.out;
    String prefix = null;
    if (resultFile != null) {
      File outfile = new File(resultFile);
      outfile.getAbsoluteFile().getParentFile().mkdirs();
      prefix = outfile.getName().split("\\.")[0];
      try {
        out = new PrintStream(outfile);
      } catch (FileNotFoundException e) {
        System.err.println("Cannot write to: " + resultFile);
        out = System.out;
      }
    }
    SMTLibExportWrapper smtWrapper = new SMTLibExportWrapper(back, out);
    if (singleQueryFolder != null) {
      smtWrapper.setOutFolder(singleQueryFolder, prefix);
    }
    return smtWrapper;
  }
}
