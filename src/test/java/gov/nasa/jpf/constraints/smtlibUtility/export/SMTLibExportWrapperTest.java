package gov.nasa.jpf.constraints.smtlibUtility.export;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.*;
import gov.nasa.jpf.constraints.smtlibUtility.solver.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

public class SMTLibExportWrapperTest {

    @Test(groups = {"jsmtlib", "base"})
    public void testSMTLibExport() {

        DontKnowSolver back = new DontKnowSolver();
        SMTLibExportWrapper se = new SMTLibExportWrapper( back, System.out );

        Variable x = new Variable(BuiltinTypes.BOOL, "x");
        Variable y = new Variable(BuiltinTypes.SINT32, "y");
        Constant c = new Constant(BuiltinTypes.SINT32, 3);

        IfThenElse ite = new IfThenElse(x,
                new NumericCompound<>(y, NumericOperator.PLUS, c),
                new NumericCompound<>(y, NumericOperator.MINUS, c));

        Expression<Boolean> expr = new NumericBooleanExpression(y, NumericComparator.GT, ite);

        //System.out.println(expr);
        se.isSatisfiable(expr);
    }
}
