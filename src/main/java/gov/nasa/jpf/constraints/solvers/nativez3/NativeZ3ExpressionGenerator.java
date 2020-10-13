/*
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */
package gov.nasa.jpf.constraints.solvers.nativez3;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.ReExpr;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.SeqExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import com.microsoft.z3.enumerations.Z3_lbool;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BooleanExpression;
import gov.nasa.jpf.constraints.expressions.BooleanOperator;
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
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.RegExBooleanExpression;
import gov.nasa.jpf.constraints.expressions.RegExCompoundOperator;
import gov.nasa.jpf.constraints.expressions.RegExOperator;
import gov.nasa.jpf.constraints.expressions.RegexCompoundExpression;
import gov.nasa.jpf.constraints.expressions.RegexOperatorExpression;
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
import gov.nasa.jpf.constraints.types.FloatingPointType;
import gov.nasa.jpf.constraints.types.IntegerType;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.RealType;
import gov.nasa.jpf.constraints.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;

public class NativeZ3ExpressionGenerator extends AbstractExpressionVisitor<Expr, Void> {
	protected static Logger logger = Logger.getLogger("constraints");
	protected final Context ctx;
	protected final Solver solver;
	protected final BoolExpr tainted;

	//	protected final Set<IDisposable> protect;
//	protected final List<IDisposable> own = new ArrayList<IDisposable>();
	protected final Map<Variable<?>, Expr> variables;
	protected int count;
	private Map<String, FuncDecl> funcDecls = new HashMap<>();

	public NativeZ3ExpressionGenerator(Context ctx, Solver solver) throws Z3Exception {
		this.ctx = ctx;
		this.solver = solver;
//		this.protect = new HashSet<IDisposable>();
		this.tainted = (BoolExpr) ctx.mkFreshConst("__tainted", ctx.getBoolSort());
//		this.protect.add(tainted);
//		this.own.add(tainted);
		this.variables = new HashMap<Variable<?>, Expr>();

		this.count = 0;
	}

	protected NativeZ3ExpressionGenerator(NativeZ3ExpressionGenerator parent) throws Z3Exception {
		this.ctx = parent.ctx;
		this.solver = parent.solver;

		this.variables = new HashMap<Variable<?>, Expr>(parent.variables);
//		this.protect = new HashSet<IDisposable>(parent.protect);
		this.tainted = parent.tainted;

		this.count = parent.count;
	}

	protected static void uncheckedDispose(Object... disposables) {
//		for (int i = 0; i < disposables.length; i++) {
//			try {
//				IDisposable disp = disposables[i];
//				if (disp != null) {
//					disp.dispose();
//				}
//			} catch (Throwable t) {
//			}
//		}
	}


	public Model recheckUntainted() throws Z3Exception {
		solver.push();
		BoolExpr untainted = ctx.mkNot(tainted);
		solver.add(untainted);
		Status r = solver.check();
		Model m = null;
		if (r == Status.SATISFIABLE) {
			m = solver.getModel();
		}
		solver.pop();
		return m;
	}

	public BoolExpr generateAssertion(Expression<Boolean> e) throws Z3Exception {
		logger.finer("assertion: " + e.toString());
		return (BoolExpr) visit(e, null);
	}


	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api
	 * .Variable, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(Variable<E> v, Void data) {
		return getOrCreateVar(v);
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .Constant, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(Constant<E> c, Void data) {
		Type<E> type = c.getType();
		try {
			if (type.equals(BuiltinTypes.BOOL)) {
				return ctx.mkBool(((Boolean) c.getValue()).booleanValue());
			}
			if (type.equals(BuiltinTypes.REGEX)) {
				return ctx.mkToRe(ctx.mkString((String) c.getValue()));
			}
			if (type.equals(BuiltinTypes.STRING)) {
				return ctx.mkString((String) c.getValue());
			}
			if (type instanceof BVIntegerType) {
				BVIntegerType<? super E> bvt = (BVIntegerType<? super E>) type;
				int bits = bvt.getNumBits();
				E v = c.getValue();
				byte[] zero = {0};
				if (v instanceof Byte) {
					return ctx.mkBV(new Byte((Byte) v).intValue(), bits);
				}
				if (v instanceof Integer) {
					return ctx.mkBV((Integer) v, bits);
				} else if (v instanceof Character) {
					int v0 = (int) (Character) v;
					return ctx.mkBV(v0, bits);
				} else if (v instanceof Long) {
					return ctx.mkBV((Long) v, bits);
				}
			}
			if (type instanceof IntegerType) {
				return ctx.mkInt(c.getValue().toString());
			}
			if (type instanceof RealType) {
				RealType<E> nt = (RealType<E>) type;
				// FIXME: this is imprecise for nan and infinity
				String val = nt.toPlainString(c.getValue());
				if (val.equals("Infinity") || val.equals("NaN")) {
					return getOrCreateRealVar(new Variable(type, val));
				}
				return ctx.mkReal(val);
			}
			throw new IllegalStateException("Cannot handle expression type " + type);
		}
		catch (Z3Exception ex) {
			logger.severe("Cannot handle constant " + c);
			throw new RuntimeException(ex);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .Negation, java.lang.Object)
	 */
	@Override
	public Expr visit(Negation n, Void data) {
		BoolExpr negatedExpr = null;
		try {
			negatedExpr = (BoolExpr) visit(n.getNegated());

			return ctx.mkNot(negatedExpr);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(negatedExpr);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.api.ExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions.IfThenElse, D)
	 */
	@Override
	public Expr visit(IfThenElse n, Void data) {
		BoolExpr ifCond = null;
		Expr thenExpr = null;
		Expr elseExpr = null;

		try {
			ifCond = (BoolExpr) visit(n.getIf());
			thenExpr = visit(n.getThen());
			elseExpr = visit(n.getElse());
			return ctx.mkITE(ifCond, thenExpr, elseExpr);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(ifCond, thenExpr, elseExpr);
		}

	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .NumericBooleanExpression, java.lang.Object)
	 */
	@Override
	public Expr visit(NumericBooleanExpression n, Void data) {

		Expr left = null, right = null;
		BoolExpr tmpEq = null;
		try {
			left = visit(n.getLeft(), null);
			right = visit(n.getRight(), null);

			NumericComparator cmp = n.getComparator();
			if (cmp == NumericComparator.EQ || cmp == NumericComparator.NE) {
				tmpEq = ctx.mkEq(left, right);
				BoolExpr result;
				if (cmp == NumericComparator.EQ) {
					result = tmpEq;
					tmpEq = null;
				} else {
					result = ctx.mkNot(tmpEq);
				}
				return result;
			}

			NumericType<?> lt = (NumericType<?>) n.getLeft().getType(), rt = (NumericType<?>) n.getRight().getType();

			if (lt instanceof BVIntegerType && lt.equals(rt)) {
				return makeBVComparison(n.getComparator(), lt.isSigned(), (BitVecExpr) left, (BitVecExpr) right);
			}

			left = ensureArith(left, lt);
			right = ensureArith(right, rt);
			return makeArithComparison(n.getComparator(), (ArithExpr) left, (ArithExpr) right);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(left, right, tmpEq);
		}
	}

//	private ArithExpr ensureArith(Expr expr, Type<?> type) throws Z3Exception {
//		if (expr instanceof ArithExpr) {
//			return (ArithExpr) expr;
//		}
//
//		if (expr instanceof BitVecExpr) {
//			BVIntegerType<?> bvType = (BVIntegerType<?>) type;
//			IntExpr intExp = makeBV2Int((BitVecExpr) expr, bvType);
//			safeDispose(expr);
//			return intExp;
//		}
//
//		throw new UnsupportedOperationException();
//	}

	private Expr makeBVComparison(NumericComparator comp, boolean signed, BitVecExpr left, BitVecExpr right) throws
			Z3Exception {
		switch (comp) {
			case EQ:
				return ctx.mkEq(left, right);
			case GE:
				return signed ? ctx.mkBVSGE(left, right) : ctx.mkBVUGE(left, right);
			case GT:
				return signed ? ctx.mkBVSGT(left, right) : ctx.mkBVUGT(left, right);
			case LE:
				return signed ? ctx.mkBVSLE(left, right) : ctx.mkBVULE(left, right);
			case LT:
				return signed ? ctx.mkBVSLT(left, right) : ctx.mkBVULT(left, right);
			case NE:
				BoolExpr eq = null;
				try {
					eq = ctx.mkEq(left, right);
					return ctx.mkNot(eq);
				}
				finally {
					uncheckedDispose(eq);
				}
			default:
				throw new UnsupportedOperationException("Comparator " + comp + " not supported");
		}
	}

	private Expr makeArithComparison(NumericComparator comp, ArithExpr left, ArithExpr right) throws Z3Exception {
		switch (comp) {
			case EQ:
				return ctx.mkEq(left, right);
			case GE:
				return ctx.mkGe(left, right);
			case GT:
				return ctx.mkGt(left, right);
			case LE:
				return ctx.mkLe(left, right);
			case LT:
				return ctx.mkLt(left, right);
			case NE:
				BoolExpr eq = null;
				try {
					eq = ctx.mkEq(left, right);
					return ctx.mkNot(eq);
				}
				finally {
					uncheckedDispose(eq);
				}
			default:
				throw new UnsupportedOperationException("Comparator " + comp + " not supported");
		}
	}


	@Override
	public Expr visit(FunctionExpression fe, Void data) {
		Function f = fe.getFunction();
		Expr[] args = new Expr[f.getParamTypes().length];
		try {
			for (int i = 0; i < args.length; i++) {
				args[i] = visit(fe.getArgs()[i], data);
			}

			FuncDecl fDecl = funcDecls.get(f.getName());
			if (fDecl == null) {
				Sort[] argTypes = new Sort[f.getParamTypes().length];
				for (int i = 0; i < argTypes.length; i++) {
					argTypes[i] = args[i].getSort();
				}

				// FIXME: is there a better way to determine the type?
				Sort ret = null;
				if (f.getReturnType() instanceof RealType<?>) {
					ret = ctx.getRealSort();
				} else if (f.getReturnType().equals(BuiltinTypes.BOOL)) {
					ret = ctx.getBoolSort();
				} else if (f.getReturnType() instanceof IntegerType<?>) {
					ret = ctx.getIntSort();
				} else {
					throw new RuntimeException("Function symbols for return type not supported: " + f.getReturnType());
				}

				fDecl = ctx.mkFuncDecl(f.getName(), argTypes, ret);
				funcDecls.put(f.getName(), fDecl);
			}

			return ctx.mkApp(fDecl, args);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(args);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .CastExpression, java.lang.Object)
	 */
	@Override
	public <F, E> Expr visit(CastExpression<F, E> cast, Void data) {

		Expression<F> casted = cast.getCasted();
		Type<F> ft = casted.getType();
		Type<E> tt = cast.getType();

		if (ft.equals(tt)) {
			return visit(casted, null);
		}

		Expr castedExpr = null;
		try {
			castedExpr = visit(casted, null);

			if (ft instanceof BVIntegerType) {
				return makeBitvectorCast((BitVecExpr) castedExpr, (BVIntegerType<F>) ft, tt);
			}
			if (ft instanceof IntegerType) {
				return makeIntegerCast((IntExpr) castedExpr, (IntegerType<F>) ft, tt);
			}
			if (ft instanceof RealType) {
				return makeRealCast((RealExpr) castedExpr, (NumericType<F>) ft, tt);
			}

			safeDispose(castedExpr);
			throw new IllegalStateException("Cannot handle cast from " + ft + " to " + tt);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}


//	private <F, T, TT extends Type<T>> Expr makeBitvectorCast(BitVecExpr castedExpr,
//															  BVIntegerType<F> from,
//															  TT to) throws Z3Exception {
//		try {
//			if (to instanceof BVIntegerType) {
//				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
//				if (from.getNumBits() == bvTo.getNumBits()) {
//					Expr tmp = castedExpr;
//					castedExpr = null; // prevent disposal
//					return tmp;
//				}
//				int diff = bvTo.getNumBits() - from.getNumBits();
//				if (diff > 0) {
//					if (from.isSigned()) {
//						return ctx.mkSignExt(diff, castedExpr);
//					}
//					return ctx.mkZeroExt(diff, castedExpr);
//				}
//				return ctx.mkExtract(bvTo.getNumBits() - 1, 0, castedExpr);
//			}
//			if (to instanceof IntegerType) {
//				//return ctx.mkBV2Int(castedExpr, from.isSigned());
//				return makeBV2Int(castedExpr, from);
//			}
//			if (to instanceof RealType) {
//				if (to instanceof FloatingPointType) {
//					FloatingPointType<?> ft = (FloatingPointType<?>) to;
//					int bitsAvail = ft.getSignificantBits() + 1;
//					if (bitsAvail < from.getNumBits()) {
//						BigInteger mask = BigInteger.valueOf(1L)
//													.shiftLeft(from.getNumBits() - bitsAvail)
//													.subtract(BigInteger.valueOf(1))
//													.shiftLeft(bitsAvail);
//
//						BoolExpr posCheck = null, negCheck = null;
//						BoolExpr check = null;
//						BoolExpr condCheck = null;
//
//						BitVecExpr zero = null;
//						BitVecExpr maskExpr = null;
//						BitVecExpr andExpr = null;
//
//						try {
//							maskExpr = ctx.mkBV(mask.toString(), from.getNumBits());
//							zero = ctx.mkBV(0, from.getNumBits());
//							andExpr = ctx.mkBVAND(castedExpr, maskExpr);
//							posCheck = ctx.mkEq(andExpr, zero);
//							if (from.isSigned()) {
//								negCheck = ctx.mkEq(andExpr, maskExpr);
//								check = ctx.mkOr(posCheck, negCheck);
//							}
//							if (check != null) {
//								condCheck = ctx.mkOr(check, tainted);
//							} else {
//								condCheck = ctx.mkOr(posCheck, tainted);
//							}
//							solver.add(condCheck);
//						}
//						finally {
//							uncheckedDispose(posCheck, negCheck, check, zero, maskExpr, andExpr);
//						}
//					}
//				}
//				IntExpr intTmp = null;
//				try {
//					intTmp = makeBV2Int(castedExpr, from);
//					return ctx.mkInt2Real(intTmp);
//				}
//				finally {
//					uncheckedDispose(intTmp);
//				}
//			}
//			throw new IllegalArgumentException("Cannot handle bitvector cast to " + to);
//		}
//		finally {
//			safeDispose(castedExpr);
//		}
//	}


//	private IntExpr makeBV2Int(BitVecExpr expr, BVIntegerType<?> type) throws Z3Exception {
//		if (!type.isSigned()) {
//			return ctx.mkBV2Int(expr, false);
//		}
//
//		BitVecExpr exprAlias = null;
//		BitVecSort sort = null;
//		BitVecExpr zero = null;
//		BoolExpr eq1 = null, eq2 = null;
//		BoolExpr ltz = null;
//		IntExpr bv2i = null, unsigned = null;
//		IntExpr bound = null;
//		IntExpr sub = null;
//		try {
//			sort = ctx.mkBitVecSort(type.getNumBits());
//			exprAlias = (BitVecExpr) ctx.mkBVConst("__bv2i" + count++, type.getNumBits());
//			eq1 = ctx.mkEq(exprAlias, expr);
//			solver.add(eq1);
//			bv2i = ctx.mkBV2Int(exprAlias, false);
//			unsigned = ctx.mkIntConst("__bv2i" + count++);
//			eq2 = ctx.mkEq(bv2i, unsigned);
//			solver.add(eq2);
//
//			zero = (BitVecExpr) ctx.mkBV(0, type.getNumBits());
//			ltz = ctx.mkBVSLT(exprAlias, zero);
//			bound = ctx.mkInt(BigInteger.valueOf(2).pow(type.getNumBits()).toString());
//			sub = (IntExpr) ctx.mkSub(unsigned, bound);
//
//			return (IntExpr) ctx.mkITE(ltz, sub, unsigned);
//		}
//		finally {
//			uncheckedDispose(exprAlias, sort, zero, eq1, eq2, ltz, bv2i, unsigned, bound, sub);
//		}
//	}

//	private IntExpr makeReal2IntTrunc(ArithExpr real) throws Z3Exception {
//		RealExpr rAlias = null;
//		BoolExpr eq1 = null;
//		IntExpr sign = null;
//		IntExpr zero = null, minusOne = null, one = null;
//		Expr ite = null;
//		BoolExpr ltz = null;
//		BoolExpr eq = null;
//		RealExpr mul = null;
//		IntExpr r2i = null;
//		try {
//			rAlias = ctx.mkRealConst("__r2i" + count++);
//			eq1 = ctx.mkEq(rAlias, real);
//			solver.add(eq1);
//			sign = ctx.mkIntConst("__sign" + count++);
//			zero = ctx.mkInt(0);
//			ltz = ctx.mkLt(rAlias, zero);
//			one = ctx.mkInt(1);
//			minusOne = ctx.mkInt(-1);
//			ite = ctx.mkITE(ltz, minusOne, one);
//			eq = ctx.mkEq(sign, ite);
//			solver.add(eq);
//			mul = (RealExpr) ctx.mkMul(sign, rAlias);
//			r2i = ctx.mkReal2Int(mul);
//			return (IntExpr) ctx.mkMul(sign, r2i);
//		}
//		finally {
//			uncheckedDispose(rAlias, eq1, sign, zero, minusOne, one, ite, ltz, eq, mul, r2i);
//		}
//	}

//	private <F, T, TT extends Type<T>> Expr makeIntegerCast(IntExpr castedExpr, IntegerType<F> from, TT to) throws
//			Z3Exception {
//		try {
//			if (to instanceof BVIntegerType) {
//				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
//				return ctx.mkInt2BV(bvTo.getNumBits(), castedExpr);
//			}
//			if (to instanceof IntegerType) {
//				Expr tmp = castedExpr;
//				castedExpr = null; // prevent disposal
//				return tmp;
//			}
//			if (to instanceof NumericType) {
//				return ctx.mkInt2Real(castedExpr);
//			}
//			throw new IllegalStateException("Cannot handle integer cast to " + to);
//		}
//		finally {
//			safeDispose(castedExpr);
//		}
//	}
//
//	private <F, T, TT extends Type<T>> Expr makeRealCast(RealExpr castedExpr, NumericType<F> from, TT to) throws
//			Z3Exception {
//		try {
//			if (to instanceof BVIntegerType) {
//				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
//				IntExpr intTmp = null;
//				try {
//					intTmp = makeReal2IntTrunc(castedExpr);
//					return ctx.mkInt2BV(bvTo.getNumBits(), intTmp);
//				}
//				finally {
//					uncheckedDispose(intTmp);
//				}
//			}
//			if (to instanceof IntegerType) {
//				return makeReal2IntTrunc(castedExpr);
//			}
//			if (to instanceof NumericType) {
//				Expr tmp = castedExpr;
//				castedExpr = null; // prevent disposal
//				return tmp;
//			}
//			throw new IllegalStateException("Cannot handle integer cast to " + to);
//		}
//		finally {
//			safeDispose(castedExpr);
//		}
//	}


	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .NumericCompound, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(NumericCompound<E> n, Void data) {
		Expr left = null, right = null;

		try {
			left = visit(n.getLeft());
			right = visit(n.getRight());

			NumericType<E> type = (NumericType<E>) n.getType();

			if (type instanceof BVIntegerType) {
				return makeBitvectorNumericCompound(n.getOperator(), type.isSigned(), (BitVecExpr) left, (BitVecExpr) right);
			}

			return makeArithmeticNumericCompound(n.getOperator(), (ArithExpr) left, (ArithExpr) right);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(left, right);
		}
	}

//	private Expr makeBitvectorNumericCompound(NumericOperator op,
//											  boolean signed,
//											  BitVecExpr left,
//											  BitVecExpr right) throws Z3Exception {
//		switch (op) {
//			case PLUS:
//				return ctx.mkBVAdd(left, right);
//			case MINUS:
//				return ctx.mkBVSub(left, right);
//			case MUL:
//				return ctx.mkBVMul(left, right);
//			case DIV:
//				return signed ? ctx.mkBVSDiv(left, right) : ctx.mkBVUDiv(left, right);
//			case REM:
//				return signed ? ctx.mkBVSRem(left, right) : ctx.mkBVURem(left, right);
//			default:
//				throw new IllegalArgumentException("Cannot handle numeric operator " + op);
//		}
//	}

//	private Expr makeArithmeticNumericCompound(NumericOperator op, ArithExpr left, ArithExpr right) throws
//	Z3Exception {
//		switch (op) {
//			case PLUS:
//				return ctx.mkAdd(left, right);
//			case MINUS:
//				return ctx.mkSub(left, right);
//			case MUL:
//				return ctx.mkMul(left, right);
//			case DIV:
//				return ctx.mkDiv(left, right);
//			case REM:
//				if (left instanceof IntExpr && right instanceof IntExpr) {
//					return ctx.mkRem((IntExpr) left, (IntExpr) right);
//				}
//				return makeRealRemainder(left, right);
//			default:
//				throw new IllegalArgumentException("Cannot handle numeric operator " + op);
//		}
//	}

	private Expr makeRealRemainder(ArithExpr left, ArithExpr right) throws Z3Exception {
		ArithExpr lAlias = null, rAlias = null;
		BoolExpr leq = null, req = null;
		ArithExpr div = null, mul = null;
		ArithExpr r2i = null;
		try {
			lAlias = (ArithExpr) ctx.mkFreshConst("reml", left.getSort());
			rAlias = (ArithExpr) ctx.mkFreshConst("remr", right.getSort());
			leq = ctx.mkEq(lAlias, left);
			req = ctx.mkEq(rAlias, right);
			solver.add(leq, req);
			div = ctx.mkDiv(lAlias, rAlias);
			r2i = makeReal2IntTrunc(div);
			mul = ctx.mkMul(r2i, rAlias);
			return ctx.mkSub(lAlias, mul);
		}
		finally {
			uncheckedDispose(lAlias, rAlias, leq, req, div, mul, r2i);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints
	 * .expressions.PropositionalCompound,java.lang.Object)
	 */

	@Override
	public Expr visit(PropositionalCompound n, Void data) {
		BoolExpr left = null, right = null;
		try {
			left = (BoolExpr) visit(n.getLeft(), null);
			right = (BoolExpr) visit(n.getRight(), null);

			switch (n.getOperator()) {
				case AND:
					return ctx.mkAnd(left, right);
				case OR:
					return ctx.mkOr(left, right);
				case EQUIV:
					return ctx.mkEq(left, right);
				case IMPLY:
					return ctx.mkImplies(left, right);
				case XOR:
					return ctx.mkXor(left, right);
				default:
					throw new IllegalStateException("Cannot handle propositional operator " + n.getOperator());
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(left, right);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .UnaryMinus, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(UnaryMinus<E> n, Void data) {
		Expr negated = null;
		try {
			negated = visit(n.getNegated(), null);
			Type<E> type = n.getType();

			if (type instanceof BVIntegerType) {
				return ctx.mkBVNeg((BitVecExpr) negated);
			}

			return ctx.mkUnaryMinus((ArithExpr) negated);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException();
		}
		finally {
			safeDispose(negated);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .QuantifierExpression, java.lang.Object)
	 */
	@Override
	public Expr visit(QuantifierExpression q, Void data) {
		BoolExpr expr = null;
		try {
			expr = (BoolExpr) visit(q.getBody());

			List<? extends Variable<?>> bound = q.getBoundVariables();
			Expr[] boundExpr = new Expr[bound.size()];
			for (int i = 0; i < boundExpr.length; i++) {
				boundExpr[i] = visit(bound.get(i));
			}

			switch (q.getQuantifier()) {
				case EXISTS:
					return ctx.mkExists(boundExpr, expr, 0, null, null, null, null);
				default: // case FORALL:
					return ctx.mkForall(boundExpr, expr, 0, null, null, null, null);
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(expr);
		}
	}


	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 .BitvectorExpression, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(BitvectorExpression<E> bv, Void data) {
		BitVecExpr left = null, right = null;

		try {
			left = (BitVecExpr) visit(bv.getLeft());
			right = (BitVecExpr) visit(bv.getRight());

			switch (bv.getOperator()) {
				case AND:
					return ctx.mkBVAND(left, right);
				case OR:
					return ctx.mkBVOR(left, right);
				case SHIFTL:
					return ctx.mkBVSHL(left, right);
				case SHIFTR:
					return ctx.mkBVASHR(left, right);
				case SHIFTUR:
					return ctx.mkBVLSHR(left, right);
				case XOR:
					return ctx.mkBVXOR(left, right);
				default:
					throw new IllegalArgumentException("Cannot handle bitvector operator " + bv.getOperator());
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(left, right);
		}
	}

	/* (non-Javadoc)
	 * @see gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.expressions
	 * .BitvectorNegation, java.lang.Object)
	 */
	@Override
	public <E> Expr visit(BitvectorNegation<E> n, Void data) {
		BitVecExpr negated = null;

		try {
			negated = (BitVecExpr) visit(n.getNegated());

			return ctx.mkBVNot(negated);
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			safeDispose(negated);
		}
	}

	@Override
	public Expr visit(RegExBooleanExpression n, Void data) {
		Expr left = null, right = null;
		try {
			left = visit(n.getLeft(), null);
			right = visit(n.getRight(), null);
			BoolExpr result = ctx.mkInRe((SeqExpr) left, (ReExpr) right);
			return result;
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Expr visit(StringCompoundExpression n, Void data) {
		Expr main = null, src = null, dst = null, position = null, length = null, offset = null;
		StringOperator operator;
		try {
			operator = n.getOperator();
			switch (operator) {
				case AT:
					main = visit(n.getMain());
					position = visit(n.getPosition());
					return ctx.mkAt((SeqExpr) main, (IntExpr) position);
				case CONCAT:
					Expression<?>[] expressions = n.getExpressions();
					SeqExpr[] expr = new SeqExpr[expressions.length];
					for (int i = 0; i < expressions.length; i++) {
						expr[i] = (SeqExpr) visit(expressions[i], null);
					}
					return ctx.mkConcat(expr);
				case REPLACE:
					main = visit(n.getMain());
					src = visit(n.getSrc());
					dst = visit(n.getDst());
					return ctx.mkReplace((SeqExpr) main, (SeqExpr) src, (SeqExpr) dst);
				case SUBSTR:
					main = visit(n.getMain());
					offset = visit(n.getOffset());
					length = visit(n.getLength());
					return ctx.mkExtract((SeqExpr) main, (IntExpr) offset, (IntExpr) length);
				case TOSTR:
					main = visit(n.getMain());
					return ctx.intToString(main);
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Expr visit(StringIntegerExpression n, Void data) {
		Expr left = null, right = null, offset = null;
		StringIntegerOperator operator;
		try {
			operator = n.getOperator();
			left = visit(n.getLeft(), null);
			switch (operator) {
				case INDEXOF:
					right = visit(n.getRight(), null);
					offset = visit(n.getOffset(), null);
					return ctx.mkIndexOf((SeqExpr) left, (SeqExpr) right, (ArithExpr) offset);
				case LENGTH:
					return ctx.mkLength((SeqExpr) left);
				case TOINT:
					return ctx.stringToInt(left);
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Expr visit(BooleanExpression n, Void data) {
		Expr left = null, right = null;
		BooleanOperator operator;
		try {
			operator = n.getOperator();
			left = visit(n.getLeft(), null);
			right = visit(n.getRight(), null);
			BoolExpr result = ctx.mkEq(left, right);
			switch (operator) {
				case EQ:
					return result;
				case NEQ:
					return ctx.mkNot(result);
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Expr visit(StringBooleanExpression n, Void data) {
		Expr left = null, right = null;
		StringBooleanOperator operator;
		try {
			operator = n.getOperator();
			left = visit(n.getLeft(), null);
			right = visit(n.getRight(), null);
			switch (operator) {
				case EQUALS:
					return ctx.mkEq(left, right);
				case CONTAINS:
					return ctx.mkContains((SeqExpr) left, (SeqExpr) right);
				case PREFIXOF:
					return ctx.mkPrefixOf((SeqExpr) left, (SeqExpr) right);
				case SUFFIXOF:
					return ctx.mkSuffixOf((SeqExpr) left, (SeqExpr) right);
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Expr visit(RegexOperatorExpression n, Void data) {
		Expr left = null;
		RegExOperator operator = null;
		try {
			operator = n.getOperator();
			switch (operator) {
				case LOOP:
					left = visit(n.getLeft());
					return ctx.mkLoop((ReExpr) left, n.getLow(), n.getHigh());
				case KLEENEPLUS:
					left = visit(n.getLeft());
					return ctx.mkPlus((ReExpr) left);
				case KLEENESTAR:
					left = visit(n.getLeft());
					return ctx.mkStar((ReExpr) left);
				case OPTIONAL:
					left = visit(n.getLeft());
					return ctx.mkOption((ReExpr) left);
				case RANGE:
					return ctx.mkRange(ctx.mkString(String.valueOf(n.getCh1())), ctx.mkString(String.valueOf(n.getCh2())));
				case ALL:
				case ALLCHAR:
					return ctx.mkFullRe(ctx.mkReSort(ctx.mkStringSort()));
				case NOSTR:
					return ctx.mkEmptyRe(ctx.mkStringSort());
				case STRTORE:
					return ctx.mkToRe(ctx.mkString(n.getS()));
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public Expr visit(RegexCompoundExpression n, Void data) {
		Expr left = null, right = null;
		RegExCompoundOperator operator = null;
		try {
			left = visit(n.getChildren()[0], null);
			right = visit(n.getChildren()[1], null);
			operator = n.getOperator();
			switch (operator) {
				case CONCAT:
					return ctx.mkConcat((ReExpr) left, (ReExpr) right);
				case INTERSECTION:
					return ctx.mkIntersect((ReExpr) left, (ReExpr) right);
				case UNION:
					return ctx.mkUnion((ReExpr) left, (ReExpr) right);
				default:
					throw new RuntimeException();
			}
		}
		catch (Z3Exception e) {
			throw new RuntimeException();
		}

	}

	@Override
	public Expr visit(LetExpression let, Void data) {
		Expression flatLet = let.flattenLetExpression();
		return visit(flatLet, data);
	}

	private ArithExpr ensureArith(Expr expr, Type<?> type) throws Z3Exception {
		if (expr instanceof ArithExpr) {
			return (ArithExpr) expr;
		}
		if (expr instanceof BitVecExpr) {
			BVIntegerType<?> bvType = (BVIntegerType<?>) type;
			IntExpr intExp = makeBV2Int((BitVecExpr) expr, bvType);
			safeDispose(expr);
			return intExp;
		}

		throw new UnsupportedOperationException();
	}

//  private Expr makeBVComparison(NumericComparator comp, boolean signed, BitVecExpr left, BitVecExpr right) throws
//  Z3Exception {
//    switch(comp) {
//    case EQ:
//      return ctx.mkEq(left, right);
//    case GE:
//      return signed ? ctx.mkBVSGE(left, right) : ctx.mkBVUGE(left, right);
//    case GT:
//      return signed ? ctx.mkBVSGT(left, right) : ctx.mkBVUGT(left, right);
//    case LE:
//      return signed ? ctx.mkBVSLE(left, right) : ctx.mkBVULE(left, right);
//    case LT:
//      return signed ? ctx.mkBVSLT(left, right) : ctx.mkBVULT(left, right);
//    case NE:
//      BoolExpr eq = null;
//      try {
//        eq = ctx.mkEq(left, right);
//        return ctx.mkNot(eq);
//      }
//      finally {
//        uncheckedDispose(eq);
//      }
//    default:
//      throw new UnsupportedOperationException("Comparator " + comp + " not supported");
//    }
//  }
//
//  private Expr makeArithComparison(NumericComparator comp, ArithExpr left, ArithExpr right) throws Z3Exception {
//    switch(comp) {
//		case EQ:
//			return ctx.mkEq(left, right);
//		case GE:
//			return ctx.mkGe(left, right);
//		case GT:
//			return ctx.mkGt(left, right);
//		case LE:
//			return ctx.mkLe(left, right);
//		case LT:
//			return ctx.mkLt(left, right);
//		case NE:
//			BoolExpr eq = null;
//			try {
//				eq = ctx.mkEq(left, right);
//				return ctx.mkNot(eq);
//			}
//			finally {
//				uncheckedDispose(eq);
//			}
//		default:
//			throw new UnsupportedOperationException("Comparator " + comp + " not supported");
//	}
//  }

	private <F, T, TT extends Type<T>> Expr makeBitvectorCast(BitVecExpr castedExpr, BVIntegerType<F> from, TT to) throws
			Z3Exception {
		try {
			if (to instanceof BVIntegerType) {
				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
				if (from.getNumBits() == bvTo.getNumBits()) {
					Expr tmp = castedExpr;
					castedExpr = null; // prevent disposal
					return tmp;
				}
				int diff = bvTo.getNumBits() - from.getNumBits();
				if (diff > 0) {
					if (from.isSigned()) {
						return ctx.mkSignExt(diff, castedExpr);
					}
					return ctx.mkZeroExt(diff, castedExpr);
				}
				return ctx.mkExtract(bvTo.getNumBits() - 1, 0, castedExpr);
			}
			if (to instanceof IntegerType) {
				//return ctx.mkBV2Int(castedExpr, from.isSigned());
				return makeBV2Int(castedExpr, from);
			}
			if (to instanceof RealType) {
				if (to instanceof FloatingPointType) {
					FloatingPointType<?> ft = (FloatingPointType<?>) to;
					int bitsAvail = ft.getSignificantBits() + 1;
					if (bitsAvail < from.getNumBits()) {
						BigInteger mask = BigInteger.valueOf(1L)
																				.shiftLeft(from.getNumBits() - bitsAvail)
																				.subtract(BigInteger.valueOf(1))
																				.shiftLeft(bitsAvail);

						BoolExpr posCheck = null, negCheck = null;
						BoolExpr check = null;
						BoolExpr condCheck = null;

						BitVecExpr zero = null;
						BitVecExpr maskExpr = null;
						BitVecExpr andExpr = null;

						try {
							maskExpr = ctx.mkBV(mask.toString(), from.getNumBits());
							zero = ctx.mkBV(0, from.getNumBits());
							andExpr = ctx.mkBVAND(castedExpr, maskExpr);
							posCheck = ctx.mkEq(andExpr, zero);
							if (from.isSigned()) {
								negCheck = ctx.mkEq(andExpr, maskExpr);
								check = ctx.mkOr(posCheck, negCheck);
							}
							if (check != null) {
								condCheck = ctx.mkOr(check, tainted);
							} else {
								condCheck = ctx.mkOr(posCheck, tainted);
							}
							solver.add(condCheck);
						}
						finally {
							uncheckedDispose(posCheck, negCheck, check, zero, maskExpr, andExpr);
						}
					}
				}
				IntExpr intTmp = null;
				try {
					intTmp = makeBV2Int(castedExpr, from);
					return ctx.mkInt2Real(intTmp);
				}
				finally {
					uncheckedDispose(intTmp);
				}
			}
			throw new IllegalArgumentException("Cannot handle bitvector cast to " + to);
		}
		finally {
			safeDispose(castedExpr);
		}
	}

	private IntExpr makeBV2Int(BitVecExpr expr, BVIntegerType<?> type) throws Z3Exception {
		if (!type.isSigned()) {
			return ctx.mkBV2Int(expr, false);
		}

		BitVecExpr exprAlias = null;
		BitVecSort sort = null;
		BitVecExpr zero = null;
		BoolExpr eq1 = null, eq2 = null;
		BoolExpr ltz = null;
		IntExpr bv2i = null, unsigned = null;
		IntExpr bound = null;
		IntExpr sub = null;
		try {
			sort = ctx.mkBitVecSort(type.getNumBits());
			exprAlias = (BitVecExpr) ctx.mkBVConst("__bv2i" + count++, type.getNumBits());
			eq1 = ctx.mkEq(exprAlias, expr);
			solver.add(eq1);
			bv2i = ctx.mkBV2Int(exprAlias, false);
			unsigned = ctx.mkIntConst("__bv2i" + count++);
			eq2 = ctx.mkEq(bv2i, unsigned);
			solver.add(eq2);

			zero = (BitVecExpr) ctx.mkBV(0, type.getNumBits());
			ltz = ctx.mkBVSLT(exprAlias, zero);
			bound = ctx.mkInt(BigInteger.valueOf(2).pow(type.getNumBits()).toString());
			sub = (IntExpr) ctx.mkSub(unsigned, bound);

			return (IntExpr) ctx.mkITE(ltz, sub, unsigned);
		}
		finally {
			uncheckedDispose(exprAlias, sort, zero, eq1, eq2, ltz, bv2i, unsigned, bound, sub);
		}
	}

	private IntExpr makeReal2IntTrunc(ArithExpr real) throws Z3Exception {
		RealExpr rAlias = null;
		BoolExpr eq1 = null;
		IntExpr sign = null;
		IntExpr zero = null, minusOne = null, one = null;
		Expr ite = null;
		BoolExpr ltz = null;
		BoolExpr eq = null;
		RealExpr mul = null;
		IntExpr r2i = null;
		try {
			rAlias = ctx.mkRealConst("__r2i" + count++);
			eq1 = ctx.mkEq(rAlias, real);
			solver.add(eq1);
			sign = ctx.mkIntConst("__sign" + count++);
			zero = ctx.mkInt(0);
			ltz = ctx.mkLt(rAlias, zero);
			one = ctx.mkInt(1);
			minusOne = ctx.mkInt(-1);
			ite = ctx.mkITE(ltz, minusOne, one);
			eq = ctx.mkEq(sign, ite);
			solver.add(eq);
			mul = (RealExpr) ctx.mkMul(sign, rAlias);
			r2i = ctx.mkReal2Int(mul);
			return (IntExpr) ctx.mkMul(sign, r2i);
		}
		finally {
			uncheckedDispose(rAlias, eq1, sign, zero, minusOne, one, ite, ltz, eq, mul, r2i);
		}
	}

	private <F, T, TT extends Type<T>> Expr makeIntegerCast(IntExpr castedExpr, IntegerType<F> from, TT to) throws
			Z3Exception {
		try {
			if (to instanceof BVIntegerType) {
				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
				return ctx.mkInt2BV(bvTo.getNumBits(), castedExpr);
			}
			if (to instanceof IntegerType) {
				Expr tmp = castedExpr;
				castedExpr = null; // prevent disposal
				return tmp;
			}
			if (to instanceof NumericType) {
				return ctx.mkInt2Real(castedExpr);
			}
			throw new IllegalStateException("Cannot handle integer cast to " + to);
		}
		finally {
			safeDispose(castedExpr);
		}
	}

	private <F, T, TT extends Type<T>> Expr makeRealCast(RealExpr castedExpr, NumericType<F> from, TT to) throws
			Z3Exception {
		try {
			if (to instanceof BVIntegerType) {
				BVIntegerType<?> bvTo = (BVIntegerType<?>) to;
				IntExpr intTmp = null;
				try {
					intTmp = makeReal2IntTrunc(castedExpr);
					return ctx.mkInt2BV(bvTo.getNumBits(), intTmp);
				}
				finally {
					uncheckedDispose(intTmp);
				}
			}
			if (to instanceof IntegerType) {
				return makeReal2IntTrunc(castedExpr);
			}
			if (to instanceof NumericType) {
				Expr tmp = castedExpr;
				castedExpr = null; // prevent disposal
				return tmp;
			}
			throw new IllegalStateException("Cannot handle integer cast to " + to);
		}
		finally {
			safeDispose(castedExpr);
		}
	}

	private Expr makeBitvectorNumericCompound(NumericOperator op,
																						boolean signed,
																						BitVecExpr left,
																						BitVecExpr right) throws Z3Exception {
		switch (op) {
			case PLUS:
				return ctx.mkBVAdd(left, right);
			case MINUS:
				return ctx.mkBVSub(left, right);
			case MUL:
				return ctx.mkBVMul(left, right);
			case DIV:
				return signed ? ctx.mkBVSDiv(left, right) : ctx.mkBVUDiv(left, right);
			case REM:
				return signed ? ctx.mkBVSRem(left, right) : ctx.mkBVURem(left, right);
			default:
				throw new IllegalArgumentException("Cannot handle numeric operator " + op);
		}
	}

	private Expr makeArithmeticNumericCompound(NumericOperator op, ArithExpr left, ArithExpr right) throws Z3Exception {
		switch (op) {
			case PLUS:
				return ctx.mkAdd(left, right);
			case MINUS:
				return ctx.mkSub(left, right);
			case MUL:
				return ctx.mkMul(left, right);
			case DIV:
				return ctx.mkDiv(left, right);
			case REM:
				if (left instanceof IntExpr && right instanceof IntExpr) {
					return ctx.mkRem((IntExpr) left, (IntExpr) right);
				}
				return makeRealRemainder(left, right);
			default:
				throw new IllegalArgumentException("Cannot handle numeric operator " + op);
		}
	}


//	private Expr makeRealRemainder(ArithExpr left, ArithExpr right) throws Z3Exception {
//		ArithExpr lAlias = null, rAlias = null;
//		BoolExpr leq = null, req = null;
//		ArithExpr div = null, mul = null;
//		ArithExpr r2i = null;
//		try {
//			lAlias = (ArithExpr) ctx.mkFreshConst("reml", left.getSort());
//			rAlias = (ArithExpr) ctx.mkFreshConst("remr", right.getSort());
//			leq = ctx.mkEq(lAlias, left);
//			req = ctx.mkEq(rAlias, right);
//			solver.add(leq, req);
//			div = ctx.mkDiv(lAlias, rAlias);
//			r2i = makeReal2IntTrunc(div);
//			mul = ctx.mkMul(r2i, rAlias);
//			return ctx.mkSub(lAlias, mul);
//		}
//		finally {
//			uncheckedDispose(lAlias, rAlias, leq, req, div, mul, r2i);
//		}
//	}

	protected Expr getOrCreateVar(Variable<?> v) {
		Type<?> type = v.getType();
		if (type.equals(BuiltinTypes.BOOL)) {
			return getOrCreateBoolVar(v);
		}
		if (type instanceof BVIntegerType) {
			return getOrCreateBVVar((Variable<?>) v);
		}
		if (type instanceof IntegerType) {
			return getOrCreateIntVar((Variable<?>) v);
		}
		if (type instanceof RealType) {
			return getOrCreateRealVar((Variable<?>) v);
		}
		if (type instanceof BuiltinTypes.StringType) {
			return getOrCreateStringVar((Variable<?>) v);
		}
		throw new IllegalArgumentException("Cannot handle variable type " + type);
	}

	private Expr getOrCreateStringVar(Variable<?> v) {
		Expr ret = this.variables.get(v);
		if (ret != null) {
			return (SeqExpr) ret;
		}

		Expr var = createSeqVar(v);
		this.variables.put(v, var);
		return var;
	}

	protected Expr createSeqVar(Variable<?> v) {
		try {
			// define var
			SeqExpr z3Var = (SeqExpr) ctx.mkConst(v.getName(), ctx.getStringSort());

			// logger.fine("Creating boolean variable " + v.getName());
			return z3Var;
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}


	protected Expr getOrCreateBoolVar(Variable<?> v) {
		Expr ret = this.variables.get(v);
		if (ret != null) {
			return (BoolExpr) ret;
		}

		Expr var = createBoolVar(v);
		this.variables.put(v, var);
//		this.protect.add(var);
//		this.own.add(var);

		return var;
	}

	protected Expr createBoolVar(Variable<?> v) {
		try {
			// define var
			BoolExpr z3Var = (BoolExpr) ctx.mkConst(v.getName(), ctx.getBoolSort());

			// logger.fine("Creating boolean variable " + v.getName());

			return z3Var;
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	protected BitVecExpr getOrCreateBVVar(Variable<?> v) {
		Expr ret = this.variables.get(v);
		if (ret != null) {
			return (BitVecExpr) ret;
		}

		BitVecExpr var = createBVVar(v);
		this.variables.put(v, var);
//	  this.protect.add(var);
//	  this.own.add(var);

		return var;
	}

	protected BitVecExpr createBVVar(Variable<?> v) {
		try {
			BVIntegerType<?> type = (BVIntegerType<?>) v.getType();
			BitVecExpr z3Var = ctx.mkBVConst(v.getName(), type.getNumBits());
			return z3Var;
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	protected IntExpr getOrCreateIntVar(Variable<?> v) {
		Expr ret = this.variables.get(v);
		if (ret != null) {
			return (IntExpr) ret;
		}

		IntExpr var = createIntVar(v);
		this.variables.put(v, var);
//		this.protect.add(var);
//		this.own.add(var);

		return var;
	}

	protected IntExpr createIntVar(Variable<?> v) {
		try {
			// define var
			IntExpr z3Var = ctx.mkIntConst(v.getName());

			IntegerType<?> type = (IntegerType<?>) v.getType();
			BigInteger min = type.getMinInt();
			BigInteger max = type.getMaxInt();

			// assert bounds
			if (min != null) {
				IntExpr intExp = null;
				BoolExpr ge = null;
				try {
					intExp = ctx.mkInt(min.toString());
					ge = ctx.mkGe(z3Var, intExp);
					solver.add(ge);
				}
				finally {
					uncheckedDispose(intExp, ge);
				}
			}
			if (max != null) {
				IntExpr intExp = null;
				BoolExpr le = null;
				try {
					intExp = ctx.mkInt(max.toString());
					le = ctx.mkLe(z3Var, intExp);
					solver.add(le);
				}
				finally {
					uncheckedDispose(intExp, le);
				}
			}

			return z3Var;
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	protected RealExpr getOrCreateRealVar(Variable<?> v) {
		Expr ret = this.variables.get(v);
		if (ret != null) {
			return (RealExpr) ret;
		}

		RealExpr var = createRealVar(v);
		this.variables.put(v, var);
//		this.protect.add(var);
//		this.own.add(var);

		return var;
	}

	/*
	protected RealExpr getReal(double d) {
		try {
		Real r = new Real(d);

			RealExpr e = ctx.mkReal(r.den, r.num);
			
			if (r.pow != 0) {
				RealExpr exp = null, base = null;
				ArithExpr pwr = null;
				RealExpr oldE = e;
				try {
					exp = ctx.mkReal(r.pow, 1);
					base = ctx.mkReal(10, 1);
					pwr = ctx.mkPower(base, exp);
					e = (RealExpr) ctx.mkMul(oldE, pwr);
				} finally {
					uncheckedDispose(exp, base, pwr, oldE);
				}
			}

			return e;
		} catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}
	*/

	protected RealExpr createRealVar(Variable<?> v) {
		try {
			RealExpr z3Var = ctx.mkRealConst(v.getName());

			NumericType<?> type = (NumericType<?>) v.getType();

			BigDecimal min = type.getMin();
			BigDecimal max = type.getMax();

			// assert bounds
			if (min != null) {
				RealExpr real = null;
				BoolExpr ge = null;
				try {
					real = ctx.mkReal(min.toPlainString());
					ge = ctx.mkGe(z3Var, real);
					solver.add(ge);
				}
				finally {
					uncheckedDispose(real, ge);
				}
			}
			if (max != null) {
				RealExpr real = null;
				BoolExpr le = null;
				try {
					real = ctx.mkReal(max.toPlainString());
					le = ctx.mkLe(z3Var, real);
					solver.add(le);
				}
				finally {
					uncheckedDispose(real, le);
				}
			}
			return z3Var;

		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	protected BoolExpr getBoolean(boolean b) {
		try {
			return b ? ctx.mkTrue() : ctx.mkFalse();
		}
		catch (Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	public void dispose() {
//	  synchronized(own) {
//  		for (IDisposable d : own) {
//  			try {
//  				d.dispose();
//  			} catch (Throwable t) {
//  			}
//  		}
//  		own.clear();
//	  }
	}

	protected void finalize() {
		dispose();
	}

	protected void safeDispose(Object... disposables) {
//		for (int i = 0; i < disposables.length; i++) {
//			IDisposable disp = disposables[i];
//			if (disp == null || protect.contains(disp)) {
//				continue;
//			}
//			try {
//				disp.dispose();
//			}
//			catch (Throwable t) {
//			}
//		}
	}

	NativeZ3ExpressionGenerator createChild() throws Z3Exception {
		return new NativeZ3ExpressionGenerator(this);
	}

	public boolean isTainted(Model model) throws Z3Exception {

		BoolExpr eval = (BoolExpr) model.eval(tainted, false);

		try {
			return (eval.getBoolValue() == Z3_lbool.Z3_L_TRUE);
		}
		finally {
			safeDispose(eval);
		}
	}

}
