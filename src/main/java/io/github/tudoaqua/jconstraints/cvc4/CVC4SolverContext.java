package io.github.tudoaqua.jconstraints.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Result;
import edu.stanford.CVC4.SExpr;
import edu.stanford.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

public class CVC4SolverContext extends SolverContext {

	private ExprManager em;
	private SmtEngine ctx;

	private HashMap<Variable, Expr> vars;
	private LinkedList<HashMap<Variable, Expr>> varsHistory;

	public CVC4SolverContext() {
		em = new ExprManager();
		ctx = new SmtEngine(em);
		ctx.setOption("produce-models", new SExpr(true));
		ctx.setOption("output-language", new SExpr("cvc4"));
		ctx.setOption("strings-exp", new SExpr(true));
		vars = new HashMap<>();
		varsHistory = new LinkedList<>();
		varsHistory.push(new HashMap());
	}

	@Override
	public void push() {
		ctx.push();
		varsHistory.push(new HashMap(vars));
	}

	@Override
	public void pop() {
		ctx.pop();
		vars = varsHistory.pop();
	}

	@Override
	public void pop(int i) {
		for (int j = 0; j < i; j++) {
			this.pop();
		}
	}

	/**
	 * The valuation is only filled with data, if the expressions in the context are satisfiable.
	 */
	@Override
	public ConstraintSolver.Result solve(Valuation valuation) {
		Result res = ctx.checkSat();
		if (res.toString().toLowerCase().equals("sat")) {
			CVC4Solver.getModel(valuation, vars, ctx);
		}
		return CVC4Solver.convertCVC4Res(res);
	}


	@Override
	public void add(List<Expression<Boolean>> list) {
		CVC4ExpressionGenerator gen = new CVC4ExpressionGenerator(em, vars);
		for (Expression<Boolean> l : list) {
			Expr expr = gen.generateExpression(l);
			ctx.assertFormula(expr);
		}
		vars = gen.getVars();
	}


	@Override
	public void dispose() {
		ctx.delete();
	}
}
