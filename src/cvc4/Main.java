package cvc4;

import java.util.Properties;

import cvc4.CVC4SolverProvider;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class Main {
	public static void main(String[] args) {
		 Variable x = new Variable(BuiltinTypes.INTEGER, "x");
		    Variable a = new Variable(BuiltinTypes.INTEGER, "a");
		    Variable b = new Variable(BuiltinTypes.INTEGER, "b");

		    Constant zero = new Constant(BuiltinTypes.INTEGER, 0);

		    Expression<Boolean> expr = new NumericBooleanExpression(
		            x, 
		            NumericComparator.EQ,
		            new NumericCompound<>(a, NumericOperator.PLUS, b));                

		    expr = ExpressionUtil.and(expr,
		            new NumericBooleanExpression(a, NumericComparator.GT, zero),
		            new NumericBooleanExpression(b, NumericComparator.LT, zero));
		    System.out.println(expr);
		    Properties conf = new Properties();     
	        conf.setProperty("symbolic.dp", "cvc4");
	        conf.setProperty("cvc4.options", "cvc4Logic=QF_LIRA");
	        ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	        factory.registerProvider(new CVC4SolverProvider());
	        ConstraintSolver solver = factory.createSolver();
	        Valuation val = new Valuation();
	        Result result=solver.solve(expr, val);
	        System.out.println("Result: "+result.toString());
		}
	}
