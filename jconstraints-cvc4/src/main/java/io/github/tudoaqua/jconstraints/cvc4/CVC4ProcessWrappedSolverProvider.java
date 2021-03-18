package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import gov.nasa.jpf.constraints.solvers.encapsulation.ProcessWrapperSolver;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class CVC4ProcessWrappedSolverProvider implements
    ConstraintSolverProvider {
  @Override
  public String[] getNames() {
    return new String[] {"cvc4process", "CVC4PROCESS"};
  }

  @Override
  public ConstraintSolver createSolver(Properties config) {
    Map<String, String> options = new HashMap<>();
    if (!config.containsKey("cvc4process.options")) {
    } else {
      String conf = config.getProperty("cvc4process.options").trim();
      String[] opts = conf.split(";");
      for (String o : opts) {
        o = o.trim();
        if (o.length() >= 1) {
          String[] val = o.split("=");
          options.put(val[0].trim(), val[1].trim());
        }
      }
    }
    ProcessWrapperSolver solver;

    if(options.containsKey("java")){
      solver = new ProcessWrapperSolver("cvc4",  options.get("java"));
    }else{
      solver = new ProcessWrapperSolver("cvc4");
    }
    return solver;
  }
}
