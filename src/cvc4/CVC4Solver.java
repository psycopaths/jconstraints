package cvc4;

import java.util.Map;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.SExpr;
import edu.nyu.acsys.CVC4.SmtEngine;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;

public class CVC4Solver extends ConstraintSolver{
	
	ExprManager em;
	SmtEngine smt;
	


  private static void prefixPrintGetValue(SmtEngine smt, Expr e, int level) {
    for(int i = 0; i < level; ++i) { System.out.print('-'); }
    System.out.println("smt.getValue(" + e + ") -> " + smt.getValue(e));

    if(e.hasOperator()) {
      prefixPrintGetValue(smt, e.getOperator(), level + 1);
    }

    for(int i = 0; i < e.getNumChildren(); ++i) {
      Expr curr = e.getChild(i);
      prefixPrintGetValue(smt, curr, level + 1);
    }
  }

	
	public CVC4Solver(Map<String, String> options) {
		System.loadLibrary("cvc4jni");
		em= new ExprManager();
		smt= new SmtEngine(em);
		//if(options.containsKey("cvc4Logic")){
		//	System.out.println("CVC4 Logic: "+options.get("cvc4Logic"));
			// smt.setLogic(options.get("cvc4Logic").trim());
		smt.setLogic("QF_NRA");
		
	  smt.setOption("produce-models", new SExpr(true)); // Produce Models
	    smt.setOption("output-language", new SExpr("cvc4")); // output-language
	    smt.setOption("default-dag-thresh", new SExpr(0));
	}
	
	
	@Override
	public Result solve(Expression<Boolean> f, Valuation result) {
		CVC4ExpressionGenerator gen = new CVC4ExpressionGenerator();
		Expr expr=gen.generateExpression(f,em);
		
		//System.out.println("Class expr: "+expr.getClass());
		smt.assertFormula(expr);
		Result resJC= Result.DONT_KNOW;
		edu.nyu.acsys.CVC4.Result resCVC= smt.checkSat(em.mkConst(true));
				
		if(resCVC.toString().equals("sat")){prefixPrintGetValue(smt, expr, 0);}
		System.out.println();
		if(resCVC.toString().equals("sat")) {
			resJC=Result.SAT;
		}else
		{
			if(resCVC.toString().equals("unsat")) {
				resJC=Result.UNSAT;
			}
		}
		//smt.getValue(expr);
		
		//TO-DO Valuation
		return resJC;
	}

}
