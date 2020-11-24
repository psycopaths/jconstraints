package gov.nasa.jpf.constraints.solvers.encapsulation;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

public class ProcessWrapperContext extends SolverContext {

  private final ProcessWrapperSolver solver;
  private Stack<List<Expression>> stack;
  private List<Expression> current;

  public ProcessWrapperContext(String name) {
    stack = new Stack<>();
    current = new LinkedList<>();
    solver = new ProcessWrapperSolver(name);
  }

  public String getName() {
    return solver.getName();
  }

  @Override
  public void push() {
    stack.push(current);
    current = new LinkedList<>();
  }

  @Override
  public void pop(int n) {
    for (int i = 0; i < n; i++) {
      current = stack.pop();
    }
  }

  @Override
  public Result solve(Valuation val) {
    Expression test = getCurrentExpression();
    Result res = solver.solve(test, val);
    //    if (res.equals(Result.SAT)) {
    //      assert (Boolean) test.evaluate(val);
    //    }
    return res;
  }

  public Expression getCurrentExpression() {
    Expression test = ExpressionUtil.TRUE;
    for (List<Expression> list : stack) {
      for (Expression e : list) {
        test = ExpressionUtil.and(test, e);
      }
    }
    for (Expression e : current) {
      test = ExpressionUtil.and(test, e);
    }
    return test;
  }

  @Override
  public void add(List<Expression<Boolean>> expressions) {
    current.addAll(expressions);
  }

  @Override
  public void dispose() {
    stack = new Stack<>();
    current = new LinkedList<>();
  }
}
