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
package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.TimeOutSolvingMessage;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.lang.management.ManagementFactory;
import java.util.List;
import java.util.Objects;

public class ProcessWrapperSolver extends ConstraintSolver {

  private final String solverName;
  String jconstraintsJar;
  private String jConstraintsExtensionsPath;
  private String javaBinary;

  private Process solver;
  private ObjectOutputStream inObject;
  private BufferedInputStream bes;
  private BufferedInputStream bos;
  private ObjectInputStream outObject;

  public ProcessWrapperSolver(String solver) {
    this.solverName = solver;
    solver = null;
    inObject = null;
    bes = null;
    bos = null;
    outObject = null;

    List<String> env = ManagementFactory.getRuntimeMXBean().getInputArguments();
    jConstraintsExtensionsPath = "";
    for (String s : env) {
      if (s.startsWith("-Djconstraints.extension.path")) {
        jConstraintsExtensionsPath = s;
        break;
      }
    }

    jconstraintsJar =
        Objects.requireNonNull(
            new File(".").list((dir, name) -> name.matches("jconstraints(?:.*)jar")))[0];
    javaBinary = "java";
  }

  public ProcessWrapperSolver(String solver, String javaBinary) {
    this(solver);
    if (!javaBinary.equals("")) {
      this.javaBinary = javaBinary;
    }
  }

  @Override
  public synchronized Result solve(Expression<Boolean> f, Valuation result) {
    try {
      return runSolverProcess(f, result);
    } catch (IOException | ClassNotFoundException e) {
      logCallToSolver(f);
      e.printStackTrace();
      return Result.DONT_KNOW;
    } catch (InterruptedException e) {
      solver = null;
      outObject = null;
      System.out.println("Restart required");
      return solve(f, result);
    }
  }

  @Override
  public SolverContext createContext() {
    return new ProcessWrapperContext(solverName, javaBinary);
  }

  private Result runSolverProcess(Expression f, Valuation result)
      throws IOException, InterruptedException, ClassNotFoundException {
    if (solver == null) {
      ProcessBuilder pb = new ProcessBuilder();
      pb.command(
          javaBinary,
          "-ea",
          "-cp",
          jconstraintsJar,
          jConstraintsExtensionsPath,
          "gov.nasa.jpf.constraints.solvers.encapsulation.SolverRunner",
          "-s",
          solverName);
      solver = pb.start();
      registerShutdown(solver);

      OutputStream inSolver = solver.getOutputStream();
      inObject = new ObjectOutputStream(inSolver);
      InputStream errSolver = solver.getErrorStream();
      bes = new BufferedInputStream(errSolver);
      InputStream outSolver = solver.getInputStream();
      bos = new BufferedInputStream(outSolver);
    }
    if (solver.isAlive()) {
      inObject.writeObject(f);
      inObject.flush();
      while (bos.available() == 0 && bes.available() == 0) {
        // Thread.sleep(5);
      }
      if (!checkBes(bes)) {
        if (outObject == null) {
          outObject = new ObjectInputStream(bos);
        }
        Object start = (StartSolvingMessage) outObject.readObject();
      }
      while (bos.available() == 0 && bes.available() == 0) {
        Thread.sleep(1);
      }
      if (!checkBes(bes)) {
        Object done = outObject.readObject();
        if (done instanceof StopSolvingMessage) {
          Object o = outObject.readObject();

          if (o instanceof SolvingResult) {
            SolvingResult res = (SolvingResult) o;
            if (res.getResult().equals(Result.SAT)) {
              for (ValuationEntry e : res.getVal()) {
                result.addEntry(e);
              }
              assert (Boolean) f.evaluate(result);
            }
            return res.getResult();
          }
        } else if (done instanceof TimeOutSolvingMessage) {
          System.out.println("Timeout in process Solver");
          solver.destroyForcibly();
        }
      }
    }
    return Result.DONT_KNOW;
  }

  private void registerShutdown(Process solver) {
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread(
                () -> {
                  try {
                    System.out.println("Shutdown hock");
                    if (solver.isAlive()) {
                      inObject.writeObject(new StopSolvingMessage());
                    }
                  } catch (IOException e) {
                    e.printStackTrace();
                    solver.destroyForcibly();
                  }
                }));
  }

  private boolean checkBes(BufferedInputStream bes) throws IOException, ClassNotFoundException {
    if (bes.available() > 0) {
      ObjectInputStream errObject = new ObjectInputStream(bes);
      Object err = errObject.readObject();
      Exception e = (Exception) err;
      e.printStackTrace();
      throw new IOException();
    }
    return false;
  }

  private void logCallToSolver(Expression f) {
    try (FileOutputStream fo =
        new FileOutputStream("/tmp/serialized_" + solverName + Long.toString(System.nanoTime()))) {
      ObjectOutputStream oo = new ObjectOutputStream(fo);
      oo.writeObject(f);
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  @Override
  public String getName() {
    return solverName;
  }
}
