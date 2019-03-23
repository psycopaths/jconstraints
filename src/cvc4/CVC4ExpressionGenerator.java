package cvc4;

import java.util.HashMap;
import java.util.List;

import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.BooleanDoubleFunction;
import gov.nasa.jpf.constraints.types.BuiltinTypes.DoubleType;
import gov.nasa.jpf.constraints.types.IntegerType;
import gov.nasa.jpf.constraints.types.RealType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionClassifier;

public class CVC4ExpressionGenerator extends AbstractExpressionVisitor<Expr, Expr> {

	private HashMap<String, Expr> intVars;

	private HashMap<String,Expr > realVars;
	
	 ExprManager em = null;
	 
	 public Expr generateExpression(Expression<Boolean> expression, ExprManager emT) {
		 intVars = new HashMap<String, Expr>();
		 realVars = new HashMap<String, Expr>();
		 em=emT;
		Expr expr=visit(expression);
		return expr;
		 
	 }
	  
	  @Override
	  public <E> Expr visit(Constant<E> c, Expr data) {
	    return em.mkConst(new Rational(c.getValue().toString()));
	  }
	  
	  @Override
	  public Expr visit(Negation n, Expr data) {
	    //TO-DO
		  //return em.mkConst(new Rational(c.getValue());
		  return null;
	  }
	  
	  @Override
	  public <E> Expr visit(NumericBooleanExpression n, Expr data) {
	    Expr left = visit(n.getLeft(), data);
	    Expr right = visit(n.getRight(), data);
	    Expr all=null; 
	    NumericComparator cmp = n.getComparator();
	   // System.out.println("left: "+left.getClass());
	  // System.out.println("right: "+right.getClass());
	    switch(cmp) {
	    case EQ:
	    	all= em.mkExpr(Kind.EQUAL, left, right);
	      break;
	    case NE:
	    	all=em.mkExpr(Kind.NOT,left, right);
	    	break;
	    case GE:
	    	all= em.mkExpr(Kind.GEQ, left, right);
	      break;
	    case GT:
	    	all= em.mkExpr(Kind.GT, left, right);
	      break;
	    case LE:
	    	all= em.mkExpr(Kind.LEQ, left, right);
	      break;
	    case LT:
	    	all= em.mkExpr(Kind.LT, left, right);
	      break;
	      default:
	      all=em.mkConst(new Rational(0));
	    }
	   return all;
	  }
	  
	  @Override
	  public <E> Expr visit(NumericCompound<E> n, Expr data) {
		Expr left = visit(n.getLeft(), data);
		Expr right = visit(n.getRight(), data);
		Expr all=null; 
		NumericOperator op = n.getOperator();
		
	    switch(op) {
	    case PLUS:
	    	all= em.mkExpr(Kind.PLUS, left, right);
	      break;
	    case MINUS:
	    	all= em.mkExpr(Kind.MINUS, left, right);
	      break;
	    case MUL:
	    	all= em.mkExpr(Kind.MULT, left, right);
	      break;
	    case DIV:
	    	all= em.mkExpr(Kind.DIVISION, left, right);
	      break;
	    case REM: //Not supported yet
	      default:
	    	  all=em.mkConst(new Rational(0));
	    }
	    return all;
	  }
	  
	  @Override
	  public <E> Expr visit(UnaryMinus<E> n, Expr data) {
	    return visit(n.getNegated()).notExpr();
	  }

	  @Override
	  public <E> Expr visit(Variable<E> v, Expr data) {
	    Type<E> t = v.getType();
		  edu.nyu.acsys.CVC4.Type real =  em.realType();
		  edu.nyu.acsys.CVC4.Type integer =  em.integerType();
	    
	    if(t instanceof RealType) {
	    	//System.out.println("Var "+v.getName()+" Type: "+real.toString());
	    	if(realVars.containsKey(v.getName())) {
	    		return realVars.get(v.getName());
	    	}
	    	else {
	    		Expr var= em.mkVar(v.getName(), (edu.nyu.acsys.CVC4.Type) real);
	    		realVars.put(v.getName(), var);
	    		return var;
	    	}
	    } else if(t instanceof IntegerType) {
	    	if(intVars.containsKey(v.getName())) {
	    		return intVars.get(v.getName());
	    	}
	    	else {
	    		Expr var= em.mkVar(v.getName(), (edu.nyu.acsys.CVC4.Type) integer);
	    		intVars.put(v.getName(), var);
	    		return var;
	    	}
	    }
	    throw new RuntimeException("Not able to map type: "+ t.toString());
	    
	  }
	  
	  @Override
	  public <E> Expr visit(FunctionExpression<E> f, Expr data) {
		  //TO-DO
		  return null;
	  }
	  
	  @Override
	  public Expr visit(PropositionalCompound n, Expr data) {
	    Expr left = visit(n.getLeft(), data);
	    Expr right = visit(n.getRight(), data);
	    Expr all=null;
	    switch(n.getOperator()) {
	    case AND:
	    	all=em.mkExpr(Kind.AND,left,right);
	      break;
	    case OR:
	    	all=em.mkExpr(Kind.OR,left,right);
	      break;
	    case XOR:
	    	all=em.mkExpr(Kind.XOR,left, right);
	    case EQUIV:
	    case IMPLY:
	    default:
	      all=null;
	    }
	    return all;
	  }
	  
	
	}	
