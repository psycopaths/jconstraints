package gov.nasa.jpf.constraints.smtlibUtility.solver;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;

import java.util.Properties;

public class SMTLibExportSolverProvider implements ConstraintSolverProvider {

    @Override
    public String[] getNames() {
        return new String[] { SMTLibExportWrapper.NAME };
    }

    @Override
    public ConstraintSolver createSolver(Properties config) {
        String backName = config.getProperty( SMTLibExportWrapper.NAME + ".back");
        ConstraintSolverFactory f = new ConstraintSolverFactory();
        ConstraintSolver back = f.createSolver(backName);
        ConstraintSolver smtWrapper = new SMTLibExportWrapper( back, System.out );
        return smtWrapper;
    }
}
