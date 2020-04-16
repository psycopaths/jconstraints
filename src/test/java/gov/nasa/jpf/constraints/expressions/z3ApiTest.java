package gov.nasa.jpf.constraints.expressions;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Properties;

import org.smtlib.IParser;

import com.microsoft.z3.AST;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Version;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Global;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.SeqExpr;

import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;


public class z3ApiTest {	
	public static void main(String args[]) throws IOException, SMTLIBParserException, IParser.ParserException {
		String filename = "/home/lasse/Bachelorarbeit/Kaluza/sat/small/1001.corecstrs.readable.smt2";
		String f2 = "/home/lasse/Bachelorarbeit/Kaluza/sat/small/3464.corecstrs.readable.smt2"; // expected Sat but evaluated false 
		String f3 = "/home/lasse/Bachelorarbeit/Kaluza/unsat/small/22598.corecstrs.readable.smt2"; //expected unsat but evaluated true
		String f4 = "/home/lasse/Bachelorarbeit/Kaluza/sat/small/streq.readable.smt2";
		String trau ="/home/lasse/Bachelorarbeit/Kaluza/unsat/small/22670.corecstrs.readable.smt2";
		smt2FileTest(f4);
//		streqReadableSmt2();
	}
	
	public static void streqReadableSmt2(){
		HashMap<String,String>cfg = new HashMap<String,String>();
		
		Context ctx = new Context(cfg);
		
		Global.setParameter("dump_models","true");
		Global.setParameter("smt.string_solver","seqfa");
		
		IntExpr I0_2 = ctx.mkIntConst("I0_2");
		IntExpr I1_2 = ctx.mkIntConst("I1_2");
		IntExpr I2_2 = ctx.mkIntConst("I2_2");
		SeqExpr PCTEMP_LHS_1 =(SeqExpr) ctx.mkConst(ctx.mkSymbol("PCTEMP_LHS_1"),ctx.mkStringSort());
		SeqExpr T1_2 = (SeqExpr) ctx.mkConst(ctx.mkSymbol("T1_2"),ctx.mkStringSort());
		SeqExpr T2_2 = (SeqExpr) ctx.mkConst(ctx.mkSymbol("T2_2"),ctx.mkStringSort());
		SeqExpr T3_2 = (SeqExpr) ctx.mkConst(ctx.mkSymbol("T3_2"),ctx.mkStringSort());
		BoolExpr T_2 = ctx.mkBoolConst("T_2");
		BoolExpr T_4 = ctx.mkBoolConst("T_4");
		BoolExpr T_5 = ctx.mkBoolConst("T_5");
		SeqExpr var_0xINPUT_19 = (SeqExpr) ctx.mkConst(ctx.mkSymbol("var_0xINPUT_19"),ctx.mkStringSort());
		
		BoolExpr a1= ctx.mkEq(I0_2, ctx.mkSub(ctx.mkInt(5),ctx.mkInt(0)));
		BoolExpr a2= ctx.mkGe(ctx.mkInt(0),ctx.mkInt(0));
		BoolExpr a3= ctx.mkGt(ctx.mkInt(5),ctx.mkInt(0));
		BoolExpr a4	= ctx.mkEq(I2_2,I1_2);
		BoolExpr a5= ctx.mkEq(I0_2,ctx.mkLength(PCTEMP_LHS_1));
		BoolExpr a6= ctx.mkEq(var_0xINPUT_19, ctx.mkConcat(T1_2,T2_2));
		BoolExpr a7= ctx.mkEq(T2_2, ctx.mkConcat(PCTEMP_LHS_1,T3_2));
		BoolExpr a8= ctx.mkEq(I1_2,ctx.mkLength(var_0xINPUT_19));
		BoolExpr a9= ctx.mkEq(T_2,ctx.mkEq(PCTEMP_LHS_1,ctx.mkString("Hello")));
		BoolExpr a10= ctx.mkEq(T_2,ctx.mkTrue());
		BoolExpr a11= ctx.mkEq(T_4,ctx.mkEq(PCTEMP_LHS_1,ctx.mkString("hello")));
		BoolExpr a12= ctx.mkEq(T_5,ctx.mkNot(T_4));
		BoolExpr a13= ctx.mkEq(T_5,ctx.mkTrue());
		Solver solver = ctx.mkSolver();
		solver.add(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13);
		if(solver.check()==Status.SATISFIABLE) {
			System.out.println(solver.getModel());
		}
		else {
			System.out.println(Status.UNSATISFIABLE);
		}
		
	}

	public static void smt2FileTest(String filename)
    {


        System.out.println("SMT2 File test ");

        {
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("model", "true");
            Global.setParameter("smt.string_solver","z3str3");
            Context ctx = new Context(cfg);
            BoolExpr a = ctx.mkAnd(ctx.parseSMTLIB2File(filename, null, null, null, null));
            System.out.println(a);
//
//            // Iterate over the formula.
//
//            LinkedList<Expr> q = new LinkedList<Expr>();
//            q.add(a);
//            int cnt = 0;
//
           AST cur = (AST) a;
           Solver solver =ctx.mkSolver();
           solver.add((BoolExpr)cur);
           System.out.println(solver.check());
           if(solver.check()==Status.SATISFIABLE) {
        	   System.out.println(solver.getModel().toString());
           }
// 
//        }
//
   }
    }
}
