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
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import java.io.PrintStream;

public class SMTLibExportWrapper extends ConstraintSolver {

  public static final String NAME = "smtlib-wrapper";

  private final ConstraintSolver back;

  private final PrintStream out;
  private String singleQueryFolder = null;
  private String queryPrefix = null;

  @Override
  public String getName() {
    return NAME;
  }

  public SMTLibExportWrapper(ConstraintSolver back, PrintStream out) {
    this.back = back;
    this.out = out;
  }

  public void setOutFolder(String folder, String queryPrefix) {
    this.singleQueryFolder = folder;
    this.queryPrefix = queryPrefix;
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    SolverContext ctx = createContext();
    return ctx.solve(f, result);
  }

  @Override
  public SolverContext createContext() {
    SMTLibExportSolverContext ctx = new SMTLibExportSolverContext(back.createContext(), out);
    if (singleQueryFolder != null) {
      ctx.setSingleQuery(singleQueryFolder, queryPrefix);
    }
    return ctx;
  }
}
