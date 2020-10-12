package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;

import java.io.PrintStream;

public class SMTLibExportWrapper extends ConstraintSolver {

    public static final String NAME = "smtlib-wrapper";

    private final ConstraintSolver back;

    private final PrintStream out;

    @Override
    public String getName() {
        return NAME;
    }

    public SMTLibExportWrapper(ConstraintSolver back, PrintStream out) {
        this.back = back;
        this.out = out;
    }

    @Override
    public Result solve(Expression<Boolean> f, Valuation result) {
        SolverContext ctx = createContext();
        return ctx.solve(f, result);
    }

    @Override
    public SolverContext createContext() {
        SMTLibExportSolverContext ctx = new SMTLibExportSolverContext( back.createContext(), out );
        return ctx;
    }
}
