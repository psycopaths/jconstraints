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
    ConstraintSolverFactory f = new ConstraintSolverFactory();
    ConstraintSolver back = f.createSolver(backName);
    PrintStream out = System.out;
    if (resultFile != null) {
      File outfile = new File(resultFile);
      outfile.getAbsoluteFile().getParentFile().mkdirs();
      try {
        out = new PrintStream(outfile);
      } catch (FileNotFoundException e) {
        System.err.println("Cannot write to: " + resultFile);
        out = System.out;
      }
    }
    ConstraintSolver smtWrapper = new SMTLibExportWrapper(back, out);
    return smtWrapper;
  }
}
