package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;

import java.io.PrintStream;
import java.util.List;

public class SMTLibExportSolverContext extends SolverContext {

	private SolverContext backCtx;

	private SMTLibExportGenContext genCtx;

	private SMTLibExportVisitor visitor;

	public SMTLibExportSolverContext(SolverContext backCtx, PrintStream out) {
		this.backCtx = backCtx;
		this.genCtx = new SMTLibExportGenContext(out);
		this.visitor = new SMTLibExportVisitor(genCtx);
	}

	@Override
	public void push() {
		genCtx.push();
		backCtx.push();
	}

	@Override
	public void pop(int n) {
		backCtx.pop(n);
		genCtx.pop(n);
	}

	@Override
	public ConstraintSolver.Result solve(Valuation val) {
		genCtx.solve();
		return backCtx.solve(val);
	}

	@Override
	public void add(List<Expression<Boolean>> expressions) {
		for (Expression<?> e : expressions) {
			visitor.transform(e);

		}
		backCtx.add(expressions);
	}

	@Override
	public void dispose() {
		// nothing
	}
}
