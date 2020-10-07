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

import edu.stanford.CVC4.BitVector;
import edu.stanford.CVC4.BitVectorExtract;
import edu.stanford.CVC4.BitVectorSignExtend;
import edu.stanford.CVC4.BitVectorZeroExtend;
import edu.stanford.CVC4.CVC4String;
import edu.stanford.CVC4.Expr;
import edu.stanford.CVC4.ExprManager;
import edu.stanford.CVC4.IntToBitVector;
import edu.stanford.CVC4.Integer;
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
import gov.nasa.jpf.constraints.expressions.LetExpression;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.StringCompoundExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.expressions.StringIntegerOperator;
import gov.nasa.jpf.constraints.expressions.StringOperator;
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
		} else if (c.getType().equals(BuiltinTypes.REAL)) {
			return em.mkConst(new Rational(c.getValue().toString()));
		} else if (c.getType().equals(BuiltinTypes.SINT32)) {
			return em.mkConst(new BitVector(32, new Integer((java.lang.Integer) c.getValue())));
		} else if (c.getType().equals(BuiltinTypes.INTEGER)) {
			return em.mkConst(new Rational(c.getValue().toString()));
		} else if (c.getType().equals(BuiltinTypes.STRING)) {
			return em.mkConst(new CVC4String(c.getValue().toString()));
		} else {
			throw new UnsupportedOperationException("Cannot convert Constant");
		}
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

		boolean bvTypes = isBVType(n.getLeft(), n.getRight());
		boolean signed = isSigned(n.getLeft(), n.getRight());

		Kind kComperator = convertNumericComparator(n.getComparator(), bvTypes, signed);

		return em.mkExpr(kComperator, left, right);
	}

	@Override
	public <E> Expr visit(NumericCompound<E> n, Expr data) {
		Expr left = visit(n.getLeft(), data);
		Expr right = visit(n.getRight(), data);

		boolean bvTypes = isBVType(n.getLeft(), n.getRight());
		boolean signed = isSigned(n.getLeft(), n.getRight());

		Kind kOperator = convertNumericOperator(n.getOperator(), bvTypes, signed);

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
			default:
				throw new UnsupportedOperationException("Cannot convert operator: " + n.toString());
		}
		return all;
	}

	@Override
	public <E> Expr visit(UnaryMinus<E> n, Expr data) {
		Expr negated = visit(n.getNegated());
		return em.mkExpr(Kind.UMINUS, negated);
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
		if (cast.getType().equals(BuiltinTypes.SINT32) && cast.getCasted().getType().equals(BuiltinTypes.INTEGER)) {
			Expr conversion = em.mkConst(new IntToBitVector(32));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT32) && cast.getCasted().getType().equals(BuiltinTypes.UINT16)) {
			Expr conversion = em.mkConst(new BitVectorZeroExtend(16));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT32) && cast.getCasted().getType().equals(BuiltinTypes.SINT16)) {
			Expr conversion = em.mkConst(new BitVectorSignExtend(16));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT32) && cast.getCasted().getType().equals(BuiltinTypes.SINT8)) {
			Expr conversion = em.mkConst(new BitVectorSignExtend(24));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT64) && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
			Expr conversion = em.mkConst(new BitVectorSignExtend(32));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.UINT16) && cast.getCasted().getType() instanceof BVIntegerType) {
			Expr conversion = em.mkConst(new BitVectorExtract(15, 0));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT16) && cast.getCasted().getType().equals(BuiltinTypes.SINT32)) {
			Expr conversion = em.mkConst(new BitVectorExtract(15, 0));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.SINT8) && cast.getCasted().getType() instanceof BVIntegerType) {
			Expr conversion = em.mkConst(new BitVectorExtract(7, 0));
			return em.mkExpr(conversion, visit(cast.getCasted(), data));
		} else if (cast.getType().equals(BuiltinTypes.INTEGER) && cast.getCasted().getType() instanceof BVIntegerType) {
			return em.mkExpr(Kind.BITVECTOR_TO_NAT, visit(cast.getCasted(), data));
		} else if (cast.getCasted() instanceof Constant) {
			if (cast.getType().equals(BuiltinTypes.INTEGER)) {
				return em.mkConst(new Rational(((Constant<F>) cast.getCasted()).getValue().toString()));
			}
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
		Kind bvOperator = convertBVOperator(bv.getOperator());
		return em.mkExpr(bvOperator, left, right);
	}

	@Override
	public Expr visit(LetExpression let, Expr data) {
		Expression e = let.flattenLetExpression();
		return visit(e, data);
	}

	@Override
	public Expr visit(StringBooleanExpression n, Expr data) {
		vectorExpr exprs = new vectorExpr(em);
		for (Expression child : n.getChildren()) {
			exprs.add(visit(child, data));
		}
		Kind operator = convertStringBooleanOpeartor(n.getOperator());
		return em.mkExpr(operator, exprs);
	}

	@Override
	public Expr visit(StringIntegerExpression n, Expr data) {
		vectorExpr exprs = new vectorExpr(em);
		for (Expression child : n.getChildren()) {
			exprs.add(visit(child, data));
		}
		Kind operator = convertStringIntegerOpeartor(n.getOperator());
		return em.mkExpr(operator, exprs);
	}


	@Override
	public Expr visit(StringCompoundExpression n, Expr data) {
		vectorExpr exprs = new vectorExpr(em);
		for (Expression child : n.getChildren()) {
			exprs.add(visit(child, data));
		}
		Kind operator = convertStringCompundOpeator(n.getOperator());
		return em.mkExpr(operator, exprs);
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
		} else if (type.equals(BuiltinTypes.STRING)) {
			return em.stringType();
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

	private Kind convertStringBooleanOpeartor(StringBooleanOperator operator) {
		switch (operator) {
			case EQUALS:
				return Kind.EQUAL;
			case CONTAINS:
				return Kind.STRING_STRCTN;
			case PREFIXOF:
				return Kind.STRING_PREFIX;
			case SUFFIXOF:
				return Kind.STRING_SUFFIX;
			default:
				throw new UnsupportedOperationException("Cannot convert the Operator: " + operator.toString());
		}
	}

	private Kind convertStringIntegerOpeartor(StringIntegerOperator operator) {
		switch (operator) {
			case INDEXOF:
				return Kind.STRING_STRIDOF;
			case TOINT:
				return Kind.STRING_STOI;
			case LENGTH:
				return Kind.STRING_LENGTH;
			default:
				throw new UnsupportedOperationException("Cannot convert the Operator: " + operator.toString());
		}
	}

	private Kind convertStringCompundOpeator(StringOperator operator) {
		switch (operator) {
			case AT:
				return Kind.STRING_CHARAT;
			case TOSTR:
				return Kind.STRING_ITOS;
			case CONCAT:
				return Kind.STRING_CONCAT;
			case SUBSTR:
				return Kind.STRING_SUBSTR;
			case REPLACE:
				return Kind.STRING_STRREPL;
			case TOLOWERCASE:
				return Kind.STRING_TOLOWER;
			case TOUPPERCASE:
				return Kind.STRING_TOUPPER;
			default:
				throw new UnsupportedOperationException("Cannot convert StringCompundOperator: " + operator.toString());
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

	private Kind convertNumericComparator(NumericComparator comparator, boolean byTypes, boolean signed) {
		if (byTypes) {
			return convertNumericComparatorBV(comparator, signed);
		} else {
			return convertNumericComparatorNBV(comparator);
		}
	}

	private Kind convertNumericComparatorNBV(NumericComparator cmp) {
		switch (cmp) {
			case EQ:
				return Kind.EQUAL;
			case NE:
				return Kind.DISTINCT;
			case GE:
				return Kind.GEQ;
			case GT:
				return Kind.GT;
			case LE:
				return Kind.LEQ;
			case LT:
				return Kind.LT;
			default:
				throw new UnsupportedOperationException("Cannot connvert NumericComparator: " + cmp.toString());
		}
	}

	private Kind convertNumericComparatorBV(NumericComparator cmp, boolean signed) {
		switch (cmp) {
			case EQ:
				return Kind.EQUAL;
			case NE:
				return Kind.DISTINCT;
			case GE:
				if (signed) {
					return Kind.BITVECTOR_SGE;
				} else {
					return Kind.BITVECTOR_UGE;
				}
			case GT:
				if (signed) {
					return Kind.BITVECTOR_SGT;
				} else {
					return Kind.BITVECTOR_UGT;
				}
			case LE:
				if (signed) {
					return Kind.BITVECTOR_SLE;
				} else {
					return Kind.BITVECTOR_ULE;
				}
			case LT:
				if (signed) {
					return Kind.BITVECTOR_SLT;
				} else {
					return Kind.BITVECTOR_ULT;
				}
			default:
				throw new UnsupportedOperationException("Cannot connvert NumericComparator: " + cmp.toString());
		}
	}

	private Kind convertNumericOperator(NumericOperator operator, boolean bvTypes, boolean signed) {
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

	private boolean isBVType(Expression left, Expression right) {
		return left.getType() instanceof ConcreteBVIntegerType || right.getType() instanceof ConcreteBVIntegerType;
	}

	private boolean isSigned(Expression left, Expression right) {
		return left.getType() instanceof ConcreteBVIntegerType && ((ConcreteBVIntegerType) left.getType()).isSigned() ||
					 right.getType() instanceof ConcreteBVIntegerType && ((ConcreteBVIntegerType) right.getType()).isSigned();
	}
}
