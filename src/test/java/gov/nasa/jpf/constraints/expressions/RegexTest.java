package gov.nasa.jpf.constraints.expressions;

import java.math.BigInteger;
import java.util.Properties;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;


public class RegexTest {
	public static void main(String[]args) {
		RegexTest t = new RegexTest();
		t.SimpleStringTests();
		}
	
	public void SimpleStringTests() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "z3");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
		System.out.println("Simple Tests");
		ConstraintSolver solver = factory.createSolver();
		Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
		Constant<String> c3 = Constant.create(BuiltinTypes.STRING, "b");
		Constant<BigInteger>i2 = Constant.create(BuiltinTypes.INTEGER,BigInteger.valueOf(0));
		StringIntegerExpression sie1= StringIntegerExpression.createIndexOf(c3,i2);
		StringBooleanExpression sbe1 = StringBooleanExpression.createEquals(StringIntegerExpression.createToInt(v1),sie1);
		Valuation val = new Valuation();
		ConstraintSolver.Result result = solver.solve(sbe1, val);
		System.out.println("result: " + result);
		System.out.println("valuation: " + val);
	}
	public void StringTest() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "z3");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	    
		System.out.println(" A string cannot overlap with two different characters. Unsat:");
		ConstraintSolver solver = factory.createSolver();
		Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
		Constant<String> c1 = Constant.create(BuiltinTypes.STRING, "b");
		Constant<String> c2 = Constant.create(BuiltinTypes.STRING, "a");
		StringCompoundExpression e1 = StringCompoundExpression.createConcat(v1,c1);
		StringCompoundExpression e2 = StringCompoundExpression.createConcat(c2,v1);
		StringBooleanExpression boolexp = StringBooleanExpression.createEquals(e1,e2);
		Valuation val = new Valuation();
		ConstraintSolver.Result result = solver.solve(boolexp, val);
		System.out.println("result: " + result);
		System.out.println("valuation: " + val);
		System.out.println("");
		System.out.println("Strings a, b, c can have a non-trivial overlap. ");
		Variable<String> v2 = Variable.create(BuiltinTypes.STRING, "v2");
		Variable<String> v3 = Variable.create(BuiltinTypes.STRING, "v3");
		Variable<String> v4 = Variable.create(BuiltinTypes.STRING, "v4");
		Constant<String> c3 = Constant.create(BuiltinTypes.STRING, "abcd");
		Constant<String> c4 = Constant.create(BuiltinTypes.STRING, "cdef");
		StringCompoundExpression e3 = StringCompoundExpression.createConcat(v2,v3);
		StringBooleanExpression boolexpr2 = StringBooleanExpression.createEquals(e3,c3);
		StringCompoundExpression e4 = StringCompoundExpression.createConcat(v3,v4);
		StringBooleanExpression boolexpr3 = StringBooleanExpression.createEquals(e4, c4);
		Valuation val2 = new Valuation();
		ConstraintSolver.Result result2 = solver.solve(ExpressionUtil.and(boolexpr2,boolexpr3),val2);
		System.out.println("result: " + result2);
		System.out.println("valuation: " + val2);
		System.out.println("");

		
	}
	public void regexMatches02() {
		Properties conf = new Properties();
	    conf.setProperty("symbolic.dp", "z3");
	    conf.setProperty("z3.options","smt.string_solver=seq");
	    System.out.println("property: " + conf.getProperty("symbolic.dp"));
//	    conf.setProperty("z3.options", "dump_models=false");

	    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
	    ConstraintSolver solver = factory.createSolver();
	    System.out.println("RegexMatches02");
	    Constant<String> string = Constant.create(BuiltinTypes.STRING, "WWWWW's Birthday is 41-17-77");
	    Constant<String> w = Constant.create(BuiltinTypes.REGEX, "W");
	    RegexOperatorExpression c09 = RegexOperatorExpression.createRange('0','9');
	    RegexOperatorExpression full = RegexOperatorExpression.createAllChar();
	    RegexOperatorExpression c03 = RegexOperatorExpression.createRange('0','3');
	    RegexOperatorExpression c59 = RegexOperatorExpression.createRange('5','9');
	    RegexCompoundExpression union = RegexCompoundExpression.createUnion(c03,c59);
	    Constant<String> c2 = Constant.create(BuiltinTypes.REGEX, "-");
	    RegexOperatorExpression loop = RegexOperatorExpression.createLoop(c09,2);
	    RegexCompoundExpression completeRegex = RegexCompoundExpression.createConcat(w,full,union,c2,loop,c2,loop);
	    Variable<String> v1 = Variable.create(BuiltinTypes.STRING, "v1");
		RegExBooleanExpression boolexpr = RegExBooleanExpression.create(completeRegex, v1);
		StringBooleanExpression boolexpr2 = StringBooleanExpression.createEquals(string,v1);
		Expression<Boolean> expr = ExpressionUtil.and(boolexpr,boolexpr2);
		Valuation val = new Valuation();
		ConstraintSolver.Result result = solver.solve(expr, val);
		System.out.println("result: " + result);
		System.out.println("valuation: " + val);
	}
}
