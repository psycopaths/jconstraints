package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import java.io.Serializable;

public class SolvingResult implements Serializable {

  private final ConstraintSolver.Result result;
  private final Valuation val;

  public SolvingResult(ConstraintSolver.Result res, Valuation val) {
    this.result = res;
    this.val = val;
  }

  public Result getResult() {
    return result;
  }

  public Valuation getVal() {
    return val;
  }
}
