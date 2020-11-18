package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

public class ProcessWrapperContext extends SolverContext {

  private final ProcessWrapperSolver solver;
  private Queue<List<Expression>> stack;
  private List<Expression> current;

  public ProcessWrapperContext(String name) {
    stack = new LinkedList<>();
    current = new LinkedList<>();
    solver = new ProcessWrapperSolver(name);
  }

  @Override
  public void push() {
    stack.add(current);
    current = new LinkedList<>();
  }

  @Override
  public void pop(int n) {
    for (int i = 0; i < n; i++) {
      pop();
    }
  }

  @Override
  public void pop() {
    current = stack.poll();
  }

  @Override
  public Result solve(Valuation val) {
    Expression test = ExpressionUtil.TRUE;
    for (List<Expression> list : stack) {
      for (Expression e : list) {
        test = ExpressionUtil.and(test, e);
      }
    }
    for (Expression e : current) {
      test = ExpressionUtil.and(test, e);
    }
    return solver.solve(test, val);
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    current.addAll(expressions);
  }

  @Override
  public void dispose() {
    stack = new LinkedList<>();
    current = new LinkedList<>();
  }
}
