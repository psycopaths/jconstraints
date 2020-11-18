package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
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
      System.exit(0);
    } catch (IOException | ClassNotFoundException | ParseException e) {
      ObjectOutputStream err = new ObjectOutputStream(System.err);
      err.writeObject(e);
      System.exit(2);
    }
  }

  private static Options getOptions() {
    Options options = new Options();
    options.addOption("s", true, "SolverName of encapsulated solver");
    return options;
  }

  private static void solve(String solverName) throws IOException, ClassNotFoundException {
    ObjectInputStream inStream = new ObjectInputStream(System.in);
    Expression expr = (Expression) inStream.readObject();
    ConstraintSolver solver = ConstraintSolverFactory.getRootFactory().createSolver(solverName);
    ObjectOutputStream out = new ObjectOutputStream(System.out);
    out.writeObject(new StartSolvingMessage());
    Valuation val = new Valuation();
    Result res = solver.solve(expr, val);
    out.writeObject(new StopSolvingMessage());
    if (res.equals(Result.SAT)) {
      assert ((Expression<Boolean>) expr).evaluate(val);
    }
    out.writeObject(new SolvingResult(res, val));
  }

  private static void silenceTheLogger() {
    Logger logger = Logger.getLogger("constraints");
    logger.getParent().setLevel(Level.OFF);
  }
}
