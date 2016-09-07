/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.expressions;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.RatNum;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;
import org.antlr.runtime.RecognitionException;
import org.testng.Assert;
import org.testng.annotations.Test;

/**
 *
 * @author falk
 */
public class DoubleTest {

    @Test
    public void expressionTest() throws RecognitionException {

        Properties conf = new Properties();
        conf.setProperty("symbolic.dp", "NativeZ3");

        Variable<Double> s2 = Variable.create(BuiltinTypes.DOUBLE, "s2");

        Constant<Double> c0 = Constant.create(BuiltinTypes.DOUBLE, 0.0);
        Constant<Double> c1 = Constant.create(BuiltinTypes.DOUBLE, 1.0);

        ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
        ConstraintSolver solver = factory.createSolver();

        Expression<Boolean> expr = ExpressionUtil.and(
                new NumericBooleanExpression(s2, NumericComparator.LT, c1),
                new NumericBooleanExpression(s2, NumericComparator.GT, c0)
        );

        System.out.println(expr.toString(3));

        Valuation val = new Valuation();
        ConstraintSolver.Result result = solver.solve(expr, val);
        System.out.println(result);
        System.out.println(val);

        Assert.assertEquals(result, Result.SAT);
    }

    @Test
    public void testZ3RealsJava() {

        Context ctx = new Context();

        RealExpr s2 = ctx.mkRealConst("s2");

        RatNum c0 = ctx.mkReal("0.0");
        RatNum c1 = ctx.mkReal("1.0");

        BoolExpr test = ctx.mkAnd(
                ctx.mkGt(s2, c0),
                ctx.mkLt(s2, c1)
        );

        System.out.println(test);
        Solver solver = ctx.mkSolver();
        solver.push();          
        solver.add(test);
        Status status = solver.check();

        Assert.assertEquals(status, Status.SATISFIABLE);
    }

}
