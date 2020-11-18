package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import java.io.EOFException;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.lang.management.ManagementFactory;
import java.util.List;

public class ProcessWrapperSolver extends ConstraintSolver {

  private final String solverName;

  public ProcessWrapperSolver(String solver) {
    this.solverName = solver;
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    ProcessBuilder pb = new ProcessBuilder();
    String jconstraintsJar =
        new File(".")
            .list(
                new FilenameFilter() {
                  @Override
                  public boolean accept(File dir, String name) {
                    return name.matches("jconstraints(?:.*)jar");
                  }
                })[0];
    List<String> env = ManagementFactory.getRuntimeMXBean().getInputArguments();

    String jConstraintsExtensionsPath = "";
    for (String s : env) {
      if (s.startsWith("-Djconstraints.extension.path")) {
        jConstraintsExtensionsPath = s;
        break;
      }
    }
    pb.command(
        "java",
        "-ea",
        "-cp",
        jconstraintsJar,
        jConstraintsExtensionsPath,
        "gov.nasa.jpf.constraints.solvers.encapsulation.SolverRunner",
        "-s",
        solverName);
    File cwd = pb.directory();
    try {
      Process solver = pb.start();
      if (solver.isAlive()) {
        OutputStream inSolver = solver.getOutputStream();
        ObjectOutputStream inObject = new ObjectOutputStream(inSolver);
        logCallToSolver(f);
        inObject.writeObject(f);
        inObject.flush();

        try {
          InputStream errSolver = solver.getErrorStream();
          ObjectInputStream errObject = new ObjectInputStream(errSolver);
          Object err = errObject.readObject();
          Exception e = (Exception) err;
          e.printStackTrace();
        } catch (EOFException e) {
          // This is okay;
        }
        InputStream outSolver = solver.getInputStream();
        ObjectInputStream outObject = new ObjectInputStream(outSolver);

        Object start = (StartSolvingMessage) outObject.readObject();
        Object done = (StopSolvingMessage) outObject.readObject();

        Object o = outObject.readObject();

        if (o instanceof SolvingResult) {
          SolvingResult res = (SolvingResult) o;
          if (res.getResult().equals(Result.SAT)) {
            for (ValuationEntry e : res.getVal()) {
              result.addEntry(e);
            }
            assert (f.evaluate(result));
          }
          return res.getResult();
        }
        return Result.DONT_KNOW;
      } else {
        int exitCode = solver.exitValue();
        InputStream errSolver = solver.getInputStream();
        ObjectInputStream errObject = new ObjectInputStream(errSolver);
        Object err = errObject.readObject();
        return Result.DONT_KNOW;
      }
    } catch (IOException | ClassNotFoundException e) {
      e.printStackTrace();
      return Result.DONT_KNOW;
    }
  }

  @Override
  public SolverContext createContext() {
    return new ProcessWrapperContext(solverName);
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
}
