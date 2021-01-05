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

import static java.lang.System.exit;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.TimeOutSolvingMessage;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public class SolverRunner {

  public static ExecutorService exec = Executors.newSingleThreadExecutor();

  private static int TIME_OUT_IN_SECONDS = 60;

  public static void main(String[] args) throws IOException {
    silenceTheLogger();
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(getOptions(), args);
      solve(cmd.getOptionValue("s"));
      exit(0);
    } catch (IOException
        | ClassNotFoundException
        | ParseException
        | InterruptedException
        | ExecutionException e) {
      ObjectOutputStream err = new ObjectOutputStream(System.err);
      err.writeObject(e);
      exit(2);
    }
  }

  private static Options getOptions() {
    Options options = new Options();
    options.addOption("s", true, "SolverName of encapsulated solver");
    return options;
  }

  private static void solve(String solverName)
      throws IOException, ClassNotFoundException, InterruptedException, ExecutionException {
    try (BufferedInputStream bin = new BufferedInputStream(System.in);
        ObjectInputStream inStream = new ObjectInputStream(bin);
        ObjectOutputStream out = new ObjectOutputStream(System.out)) {
      ConstraintSolver solver = ConstraintSolverFactory.getRootFactory().createSolver(solverName);
      while (true) {
        if (bin.available() > 0) {
          Object read = inStream.readObject();
          if (read instanceof Expression) {
            Expression expr = (Expression) read;

            out.writeObject(new StartSolvingMessage());
            Valuation val = new Valuation();
            try {
              Result res = solveWithTimeOut(solver, expr, val);
              out.writeObject(new StopSolvingMessage());
              out.writeObject(new SolvingResult(res, val));
              out.flush();
            } catch (TimeoutException e) {
              out.writeObject(new TimeOutSolvingMessage());
              exec.shutdownNow();
              break;
            }
          } else {
            StopSolvingMessage ssm = (StopSolvingMessage) read;
            break;
          }
        } else {
          // Thread.sleep(1);
        }
      }
    }
  }

  private static Result solveWithTimeOut(ConstraintSolver solver, Expression expr, Valuation val)
      throws TimeoutException, ExecutionException, InterruptedException {
    FutureTask<Result> solverRun = new FutureTask<>(() -> solver.solve(expr, val));
    exec.submit(solverRun);
    try {
      return solverRun.get(TIME_OUT_IN_SECONDS, TimeUnit.SECONDS);
    } catch (TimeoutException e) {
      solverRun.cancel(true);
      exec.shutdown();
      throw e;
    }
  }

  private static void silenceTheLogger() {
    Logger logger = Logger.getLogger("constraints");
    logger.getParent().setLevel(Level.OFF);
  }
}
