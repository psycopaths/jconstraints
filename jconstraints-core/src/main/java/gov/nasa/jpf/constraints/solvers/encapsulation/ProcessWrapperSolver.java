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
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.lang.management.ManagementFactory;
import java.util.List;

public class ProcessWrapperSolver extends ConstraintSolver {

  private final String solverName;
  String javaClassPath;
  private String jConstraintsExtensionsPath;
  private static int TIMEOUT = 60;
  private String javaBinary;

  private Process solver;
  private ObjectOutputStream inObject;
  private BufferedInputStream bes;
  private BufferedInputStream bos;
  private ObjectInputStream outObject;

  public ProcessWrapperSolver(String solver) {
    this.solverName = solver;
    inObject = null;
    bes = null;
    bos = null;
    outObject = null;

    List<String> env = ManagementFactory.getRuntimeMXBean().getInputArguments();
    jConstraintsExtensionsPath = "";
    for (String s : env) {
      if (s.startsWith("-Djconstraints.wrapper.timeout")) {
        TIMEOUT = Integer.parseInt(s.split("=")[1]);
      }
    }

    javaClassPath = System.getProperty("java.class.path");
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
          javaClassPath,
          "gov.nasa.jpf.constraints.solvers.encapsulation.SolverRunner",
          "-s",
          solverName,
          "-t",
          Integer.toString(TIMEOUT));
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
      if (!checkBes(bes, f)) {
        if (outObject == null) {
          outObject = new ObjectInputStream(bos);
        }
        Object start = (StartSolvingMessage) outObject.readObject();
      }
      while (bos.available() == 0 && bes.available() == 0) {
        Thread.sleep(1);
      }
      if (!checkBes(bes, f)) {
        Object done = outObject.readObject();
        if (done instanceof StopSolvingMessage) {
          Object o = outObject.readObject();

          if (o instanceof SolvingResult) {
            SolvingResult res = (SolvingResult) o;
            if (res.getResult().equals(Result.SAT) && result != null) {
              for (ValuationEntry e : res.getVal()) {
                result.addEntry(e);
              }
              try {
                assert (Boolean) f.evaluate(result);
              } catch (UnsupportedOperationException e) {
                // This might happen if something in the expression does not support the valuation.
              }
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

  public void shutdown() throws IOException {
    if (solver != null && solver.isAlive()) {
      StopSolvingMessage ssm = new StopSolvingMessage();
      ObjectOutputStream os = new ObjectOutputStream(solver.getOutputStream());
      os.writeObject(ssm);
      os.flush();
    }
  }

  private void registerShutdown(Process solver) {
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread(
                () -> {
                  try {
                    shutdown();
                  } catch (IOException e) {
                    e.printStackTrace();
                    solver.destroyForcibly();
                  }
                }));
  }

  private boolean checkBes(BufferedInputStream bes, Object f) throws IOException {
    if (bes.available() > 0) {
      ObjectInputStream errObject = new ObjectInputStream(bes);
      try {
        Object err = errObject.readObject();
        Exception e = (Exception) err;
        e.printStackTrace();
      } catch (ClassNotFoundException e) {
        System.out.println("f: " + f);
        logCallToSolver(f);
      }
      throw new IOException();
    }
    return false;
  }

  private void logCallToSolver(Object f) {
    String fileName = "/tmp/serialized_" + solverName + Long.toString(System.nanoTime());
    try (FileOutputStream fo = new FileOutputStream(fileName)) {
      ObjectOutputStream oo = new ObjectOutputStream(fo);
      oo.writeObject(f);
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    System.out.println("Logged an Object to: " + fileName);
  }

  @Override
  public String getName() {
    return solverName;
  }
}
