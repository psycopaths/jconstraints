package gov.nasa.jpf.constraints.expressions;

import java.math.BigInteger;
import java.util.Properties;

import org.testng.Assert;
import org.testng.annotations.Test;

import com.microsoft.z3.Global;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;


public class RegexTest {
	public static void main(String[]args) {
		RegexTest t = new RegexTest();
		t.regexMatches02();
		}
	
	public void regexMatches02() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "z3");
	    conf.setProperty("z3.options","smt.string_solver=seq");
//	    conf.setProperty("z3.options", "dump_models=false");

	    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	    ConstraintSolver solver = factory.createSolver();
	    System.out.println("RegexMatches02");
	    SolverContext ctx = solver.createContext();
	    Constant<String> string = Constant.create(BuiltinTypes.STRING, "WWWWW's Birthday is 41-17-77");
	    Constant<String> w = Constant.create(BuiltinTypes.REGEX, "W");
	    Constant<String> c09 = Constant.create(BuiltinTypes.range('0','9'),"test");
	    RegexOperatorExpression full = RegexOperatorExpression.create(Constant.create(BuiltinTypes.REGEXALL,""),RegExOperator.KLEENESTAR);
	    Constant<String> c03 = Constant.create(BuiltinTypes.range('0','3'),"test");
	    Constant<String> c59 = Constant.create(BuiltinTypes.range('5','9'),"test");
	    RegexCompoundExpression union = RegexCompoundExpression.create(c03, RegExCompoundOperator.UNION,c59);
	    Constant<String> c2 = Constant.create(BuiltinTypes.REGEX, "-");
	    RegexOperatorExpression loop = RegexOperatorExpression.create(c09,RegExOperator.LOOP, 2, 2);
	    RegexCompoundExpression completeRegex = RegexCompoundExpression.create(w, RegExCompoundOperator.CONCAT,full,union,c2,loop,c2,loop);
	    Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
		RegExBooleanExpression boolexpr = RegExBooleanExpression.create(completeRegex, v1);
		StringBooleanExpression boolexpr2 = StringBooleanExpression.create(string,v1);
		Expression<Boolean> expr = ExpressionUtil.and(boolexpr,boolexpr2);
		Valuation val = new Valuation();
		ConstraintSolver.Result result = solver.solve(expr, val);
		System.out.println("Expression: " + expr);
		System.out.println("result: " + result);
		System.out.println("valuation: " + val);
	}
	public void testToString() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "Z3");
	    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	    ConstraintSolver solver = factory.createSolver();
	    System.out.println("Neuer Test2");
	    SolverContext ctx = solver.createContext();

		Constant<String> hallo = Constant.create(BuiltinTypes.REGEX, "Hallo Welt");

		RegexOperatorExpression welt =new RegexOperatorExpression(Constant.create(BuiltinTypes.REGEX, "!"),RegExOperator.KLEENEPLUS);
		
		RegexCompoundExpression hallowelt = RegexCompoundExpression.create(hallo, RegExCompoundOperator.CONCAT, welt);
		Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
		Variable<BigInteger> i1 = Variable.create(BuiltinTypes.INTEGER, "i1");
		Constant<BigInteger> i2 = Constant.createCasted(BuiltinTypes.INTEGER, 2);
		//Variable<BigInteger> i2 = Variable.create(BuiltinTypes.INTEGER, "i2");
		NumericBooleanExpression nbe1= NumericBooleanExpression.create(i1, NumericComparator.EQ,i2);
		RegExBooleanExpression test = RegExBooleanExpression.create(hallowelt, v1);

		
		Valuation val = new Valuation();
		Valuation val2 = new Valuation();
		ConstraintSolver.Result result2 = solver.solve(nbe1, val2);
        ConstraintSolver.Result result = solver.solve(test, val);
        ctx.add(test);
        if (ctx.isSatisfiable()!=null) {
        	System.out.println("ctx.toString " +ctx.toString());
        }
        
       System.out.println("result: " + result);
       System.out.println("valuation: " +val);
       System.out.println("resul2t: " + result2);
       System.out.println("valuation2: " +val2);
//        ContextTest test = 
        
	}
}
