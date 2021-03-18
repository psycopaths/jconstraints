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

package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import java.io.IOException;
import org.testng.SkipException;
import org.testng.annotations.AfterMethod;
import org.testng.annotations.BeforeMethod;

public abstract class AbstractCVC4Test {

  protected ProcessWrapperSolver cvc4;
  protected SolverContext cvc4Context;
  protected boolean loadingFailed = false;

  @BeforeMethod
  public void initialize() {
    if (loadingFailed || System.getProperty("os.name").contains("windows")) {
      throw new SkipException("No native CVC4 support");
    }
    try {

      cvc4 = new ProcessWrapperSolver("cvc4");
      cvc4Context = cvc4.createContext();
    } catch (UnsatisfiedLinkError e) {
      loadingFailed = true;
      throw new SkipException("No native CVC4 support", e);
    }
  }

  @AfterMethod
  public void shutDownCVC4() {
    try {
      cvc4.shutdown();
    } catch (IOException e) {
      // The solver might already be crashed
    }
  }
}
