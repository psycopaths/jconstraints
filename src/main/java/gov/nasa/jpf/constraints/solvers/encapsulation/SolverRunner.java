package gov.nasa.jpf.constraints.solvers.encapsulation;

import static java.lang.System.exit;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public class SolverRunner {

  public static void main(String[] args) throws IOException {
    silenceTheLogger();
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(getOptions(), args);
      solve(cmd.getOptionValue("s"));
      exit(0);
    } catch (IOException | ClassNotFoundException | ParseException | InterruptedException e) {
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
      throws IOException, ClassNotFoundException, InterruptedException {
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
            Result res = solver.solve(expr, val);
            out.writeObject(new StopSolvingMessage());
            out.writeObject(new SolvingResult(res, val));
            out.flush();
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

  private static void silenceTheLogger() {
    Logger logger = Logger.getLogger("constraints");
    logger.getParent().setLevel(Level.OFF);
  }
}
