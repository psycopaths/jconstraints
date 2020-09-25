/**
 * Copyright 2020 TU Dortmund, Nils Schmidt und Malte Mues
 * <p>
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * <p>
 * http://www.apache.org/licenses/LICENSE-2.0
 * <p>
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */
package io.github.tudoaqua.jconstraints.cvc4;

import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.Kind;
import edu.stanford.CVC4.Rational;
import edu.stanford.CVC4.vectorExpr;
import edu.stanford.CVC4.vectorType;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BVIntegerType;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.ConcreteBVIntegerType;
import gov.nasa.jpf.constraints.types.NamedSort;
import gov.nasa.jpf.constraints.types.Type;
import io.github.tudoaqua.jconstraints.cvc4.exception.CVC4ConversionException;

import java.util.HashMap;

public class CVC4ExpressionGenerator extends AbstractExpressionVisitor<Expr, Expr> {

	private final ExprManager em;
	private HashMap<Variable, Expr> vars;
	private HashMap<String, edu.stanford.CVC4.Type> declaredTypes;
	private HashMap<Function, Expr> declaredFunctions;

	public CVC4ExpressionGenerator(ExprManager emT) {
		vars = new HashMap<>();
		this.em = emT;
		declaredTypes = new HashMap<>();
		declaredFunctions = new HashMap<>();
	}

	public CVC4ExpressionGenerator(ExprManager emT, HashMap<Variable, Expr> vars) {
		this(emT);
		this.vars = vars;
	}

	public Expr generateExpression(Expression<Boolean> expression) {
		Expr expr = visit(expression);
		return expr;

	}

	@Override
	public <E> Expr visit(Variable<E> v, Expr data) {
		Type<E> t = v.getType();
		if (vars.containsKey(v)) {
			return vars.get(v);
		} else {
			Expr var = em.mkVar(v.getName(), typeMapjConstraintsCVC4(v.getType()));
			vars.put(v, var);
			return var;
		}
	}

	@Override
	public <E> Expr visit(Constant<E> c, Expr data) {
		if (c.getType().equals(BuiltinTypes.BOOL)) {
			return em.mkConst((Boolean) c.getValue());
		}
		return em.mkConst(new Rational(c.getValue().toString()));
	}

	@Override
	public Expr visit(Negation n, Expr data) {
		Expr containted = visit(n.getNegated(), data);
		return containted.notExpr();
	}

	@Override
	public Expr visit(NumericBooleanExpression n, Expr data) {
		Expr left = visit(n.getLeft(), data);
		Expr right = visit(n.getRight(), data);
		Expr all = null;
		NumericComparator cmp = n.getComparator();
		switch (cmp) {
			case EQ:
				all = em.mkExpr(Kind.EQUAL, left, right);
				break;
			case NE:
				all = em.mkExpr(Kind.DISTINCT, left, right);
				break;
			case GE:
				all = em.mkExpr(Kind.GEQ, left, right);
				break;
			case GT:
				all = em.mkExpr(Kind.GT, left, right);
				break;
			case LE:
				all = em.mkExpr(Kind.LEQ, left, right);
				break;
			case LT:
				all = em.mkExpr(Kind.LT, left, right);
				break;
			default:
				throw new UnsupportedOperationException("Cannot connvert NumericComparator: " + cmp.toString());
		}
		return all;
	}

	@Override
	public <E> Expr visit(NumericCompound<E> n, Expr data) {
		Expr left = visit(n.getLeft(), data);
		Expr right = visit(n.getRight(), data);
		Expr all = null;
		boolean bvTypes = n.getLeft().getType() instanceof ConcreteBVIntegerType ||
						  n.getRight().getType() instanceof ConcreteBVIntegerType;
		boolean signed = n.getLeft().getType() instanceof ConcreteBVIntegerType &&
						 ((ConcreteBVIntegerType) n.getLeft().getType()).isSigned() ||
						 n.getRight().getType() instanceof ConcreteBVIntegerType &&
						 ((ConcreteBVIntegerType) n.getRight().getType()).isSigned();
		Kind kOperator = convertOperator(n.getOperator(), bvTypes, signed);

		return em.mkExpr(kOperator, left, right);
	}

	@Override
	public Expr visit(PropositionalCompound n, Expr data) {
		Expr left = visit(n.getLeft(), data);
		Expr right = visit(n.getRight(), data);
		Expr all = null;
		switch (n.getOperator()) {
			case AND:
				all = em.mkExpr(Kind.AND, left, right);
				break;
			case OR:
				all = em.mkExpr(Kind.OR, left, right);
				break;
			case XOR:
				all = em.mkExpr(Kind.XOR, left, right);
			case EQUIV:
			case IMPLY:
			default:
				all = null;
		}
		return all;
	}

	@Override
	public <E> Expr visit(UnaryMinus<E> n, Expr data) {
		return visit(n.getNegated()).notExpr();
	}


	public Expr visit(Function f, Expr data) {
		if (declaredFunctions.containsKey(f)) {
			return declaredFunctions.get(f);
		}
		vectorType functionTypes = new vectorType(em);
		for (Type t : f.getParamTypes()) {
			functionTypes.add(typeMapjConstraintsCVC4(t));
		}
		functionTypes.add(typeMapjConstraintsCVC4(f.getReturnType()));
		edu.stanford.CVC4.Type fType = em.mkFunctionType(functionTypes);
		Expr function = em.mkVar(f.getName(), fType);
		declaredFunctions.put(f, function);
		return function;
	}

	@Override
	public <E> Expr visit(FunctionExpression<E> f, Expr data) {
		Expr function = visit(f.getFunction(), data);
		vectorExpr args = new vectorExpr(em);
		for (Expression e : f.getArgs()) {
			args.add(visit(e, data));
		}
		return em.mkExpr(Kind.APPLY_UF, function, args);
	}

	@Override
	public <F, E> Expr visit(CastExpression<F, E> cast, Expr data) {
		//FIXME: This is eventually a relaxiation of the problem. But it seems to be the way CVC4 handels cast
		// internally.
		if (cast.getCasted() instanceof Variable) {
			return visit(cast.getCasted(), data);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public <E> Expr visit(IfThenElse<E> n, Expr data) {
		Expr condition = visit(n.getIf(), data);
		Expr ifPart = visit(n.getThen(), data);
		Expr elsePart = visit(n.getElse(), data);

		return em.mkExpr(Kind.ITE, condition, ifPart, elsePart);
	}

	@Override
	public <E> Expr visit(BitvectorExpression<E> bv, Expr data) {
		Expr left = visit(bv.getLeft(), data);
		Expr right = visit(bv.getRight(), data);
		Kind bvOperater = convertBVOperator(bv.getOperator());
		return em.mkExpr(bvOperater, left, right);
	}


	public HashMap<Variable, Expr> getVars() {
		return new HashMap<>(vars);
	}

	public void clearVars() {
		vars.clear();
	}

	private edu.stanford.CVC4.Type typeMapjConstraintsCVC4(Type type) {
		if (type instanceof BuiltinTypes.RealType) {
			return em.realType();
		} else if (type instanceof BuiltinTypes.BoolType) {
			return em.booleanType();
		} else if (type instanceof BuiltinTypes.BigDecimalType) {
			BuiltinTypes.BigDecimalType decimal = (BuiltinTypes.BigDecimalType) type;
			return em.realType();
		} else if (type instanceof BuiltinTypes.DoubleType) {
			BuiltinTypes.DoubleType doubleType = (BuiltinTypes.DoubleType) type;
			return em.mkFloatingPointType(64 - doubleType.getSignificantBits(), doubleType.getSignificantBits());
		} else if (type instanceof BuiltinTypes.FloatType) {
			return em.mkFloatingPointType(32 - BuiltinTypes.FLOAT.getSignificantBits(),
										  BuiltinTypes.FLOAT.getSignificantBits());
		} else if (type instanceof BuiltinTypes.BigIntegerType) {
			return em.integerType();
		} else if (type instanceof BVIntegerType) {
			return em.mkBitVectorType(((BVIntegerType<?>) type).getNumBits());
		} else if (type instanceof NamedSort) {
			if (declaredTypes.containsKey(type.getName())) {
				return declaredTypes.get(type.getName());
			} else {
				edu.stanford.CVC4.Type t = em.mkSort(type.getName());
				declaredTypes.put(type.getName(), t);
				return t;
			}

		} else {
			throw new CVC4ConversionException("Cannot convert Type: " + type.getName());
		}
	}

	private Kind convertBVOperator(BitvectorOperator operator) {
		if (BitvectorOperator.AND.equals(operator)) {
			return Kind.BITVECTOR_AND;
		} else if (BitvectorOperator.OR.equals(operator)) {
			return Kind.BITVECTOR_OR;
		} else if (BitvectorOperator.XOR.equals(operator)) {
			return Kind.BITVECTOR_XOR;
		}
		throw new UnsupportedOperationException("Cannot convert BitvectorOperator: " + operator.toString() + " yet.");
	}

	private Kind convertOperator(NumericOperator operator, boolean bvTypes, boolean signed) {
		if (bvTypes) {
			switch (operator) {
				case DIV:
					if (signed) {
						return Kind.BITVECTOR_SDIV;
					} else {
						return Kind.BITVECTOR_UDIV;
					}
				case MUL:
					return Kind.BITVECTOR_MULT;
				case REM:
					if (signed) {
						return Kind.BITVECTOR_SREM;
					} else {
						return Kind.BITVECTOR_UREM;
					}
				case PLUS:
					return Kind.BITVECTOR_PLUS;
				case MINUS:
					return Kind.BITVECTOR_SUB;
			}
		} else {
			switch (operator) {
				case PLUS:
					return Kind.PLUS;
				case MINUS:
					return Kind.MINUS;
				case REM:
					return Kind.INTS_MODULUS;
				case MUL:
					return Kind.MULT;
				case DIV:
					return Kind.DIVISION;
			}
		}
		throw new UnsupportedOperationException("Cannot convert operator: " + operator.toString());
	}
}
