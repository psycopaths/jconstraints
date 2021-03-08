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

import static gov.nasa.jpf.constraints.util.CharsetIO.wrapInUTF8PrintStream;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

public class SMTLibExportSolverContext extends SolverContext {

  private SolverContext backCtx;

  private SMTLibExportGenContext genCtx;

  private SMTLibExportVisitor visitor;

  private String singleQueryFolder = null;
  private String queryPrefix = null;
  private int queryCounter = 0;

  private Stack<List<Expression>> ctxKopie = new Stack<>();

  public SMTLibExportSolverContext(SolverContext backCtx, PrintStream out) {
    this.backCtx = backCtx;
    this.genCtx = new SMTLibExportGenContext(out);
    this.visitor = new SMTLibExportVisitor(genCtx);
    ctxKopie.push(new LinkedList<>());
  }

  @Override
  public void push() {
    genCtx.push();
    backCtx.push();
    ctxKopie.push(new LinkedList<>());
  }

  @Override
  public void pop(int n) {
    backCtx.pop(n);
    genCtx.pop(n);
    for (int i = 0; i < n; i++) {
      ctxKopie.pop();
    }
  }

  @Override
  public ConstraintSolver.Result solve(Valuation val) {
    genCtx.solve();
    if (singleQueryFolder != null) {
      makeSingleQuery();
    }
    return backCtx.solve(val);
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    for (Expression<?> e : expressions) {
      ctxKopie.peek().add(e);
      visitor.transform(e);
    }
    backCtx.add(expressions);
  }

  @Override
  public void dispose() {
    // nothing
  }

  public void setSingleQuery(String folder, String prefix) {
    this.singleQueryFolder = folder;
    this.queryPrefix = prefix;
  }

  private void makeSingleQuery() {
    Path newFileName =
        Paths.get(singleQueryFolder, queryPrefix + "_" + Integer.toString(queryCounter) + ".smt2");
    newFileName.toFile().getAbsoluteFile().getParentFile().mkdirs();
    try (FileOutputStream fos = new FileOutputStream(newFileName.toFile())) {
      PrintStream pw = wrapInUTF8PrintStream(fos);
      SMTLibExportGenContext queryCtx = new SMTLibExportGenContext(pw);
      SMTLibExportVisitor queryVisitor = new SMTLibExportVisitor(queryCtx);
      for (List<Expression> level : ctxKopie) {
        for (Expression e : level) {
          queryVisitor.transform(e);
        }
      }
      queryCtx.solve();
    } catch (IOException e) {
      e.printStackTrace();
      throw new RuntimeException(e);
    }
    ++queryCounter;
  }
}
