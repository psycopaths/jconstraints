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

package gov.nasa.jpf.constraints.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorNegation;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.CastExpression;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.NumericType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.types.TypeContext;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.antlr.runtime.tree.Tree;
import org.antlr.runtime.tree.TreeVisitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.constraints.parser.ExpressionLexer.PRIMEID;
import static gov.nasa.jpf.constraints.parser.ExpressionParser.*;


public class ASTTranslator extends TreeVisitor {

	private static class Context {
		private final Map<String, Variable<?>> vars = new HashMap<String, Variable<?>>();
		private final Context parent;

		public Context() {
			this(null);
		}

		public Context(Context parent) {
			this.parent = parent;
		}

		public void declareVariables(Collection<? extends Variable<?>> variables) {
			for (Variable<?> var : variables) {
				if (vars.put(var.getName(), var) != null) {
					throw new IllegalStateException("Duplicate declaration of variable " + var.getName());
				}
			}
		}

		public Collection<? extends Variable<?>> getVariables() {
			return vars.values();
		}

		public Context getParent() {
			return parent;
		}

		public Variable<?> lookup(String name) {
			Variable<?> var = vars.get(name);
			if (var != null) {
				return var;
			}
			if (parent != null) {
				return parent.lookup(name);
			}
			return null;
		}
	}


	private Context current = new Context();
	private final TypeContext types;

	public ASTTranslator(TypeContext types) {
		this.types = types;
	}

	public void declareVariables(Collection<? extends Variable<?>> variables) {
		this.current.declareVariables(variables);
	}

	public void pushContext() {
		Context ctx = new Context(this.current);
		this.current = ctx;
	}

	public void pushContext(Collection<? extends Variable<?>> variables) {
		pushContext();
		this.current.declareVariables(variables);
	}

	public void popContext() {
		Context currParent = current.getParent();
		if (currParent == null) {
			throw new IllegalStateException("Cannot pop root context");
		}
		current = currParent;
	}

	public Collection<? extends Variable<?>> getVariableOfTopContext() {
		return current.getVariables();
	}

	public Expression<Boolean> translateRootLogical(Tree n) throws ImpreciseRepresentationException {
		requireType(n, ROOT);
		int exprIdx = 0;
		if (n.getChildCount() > 1) {
			List<? extends Variable<?>> varDecls = translateTypedVarList(n.getChild(0));
			current.declareVariables(varDecls);
			exprIdx++;
			return translateBoolExpression(n.getChild(exprIdx));
		}
		switch (n.getChild(0).getType()) {
			case TYPED_VAR_LIST:
				List<? extends Variable<?>> varDecls = translateTypedVarList(n.getChild(0));
				current.declareVariables(varDecls);
				return null;
			default:
				return translateBoolExpression(n.getChild(0));
		}
	}

	public Variable<?> translateRootVariable(Tree n) {
		requireType(n, ROOT);
		return translateTypedVar(n.getChild(0));
	}

	public Expression translateRootArithmetic(Tree n) throws ImpreciseRepresentationException {
		requireType(n, ROOT);
		int exprIdx = 0;
		if (n.getChildCount() > 1) {
			List<? extends Variable<?>> varDecls = translateTypedVarList(n.getChild(0));
			current.declareVariables(varDecls);
			exprIdx++;
		}

		return translateArithmeticExpression(n.getChild(exprIdx));
	}

	public Expression<Boolean> translateBoolExpression(Tree n) throws ImpreciseRepresentationException {
		switch (n.getType()) {
			case FORALL:
			case EXISTS:
				return translateQuantifier(n);
			case LIMP:
			case LEQ:
			case LXOR:
			case LOR:
			case LAND:
				return translatePropositionalCompound(n);
			case EQ:
			case NE:
			case LT:
			case LE:
			case GT:
			case GE:
				return translateNumericComparison(n);
			case LNOT:
				return translateLogicalNegation(n);
			case TRUE:
				return ExpressionUtil.TRUE;
			case FALSE:
				return ExpressionUtil.FALSE;
			case QID:
			case ID:
			case PRIMEID:
				return (Expression<Boolean>) translateVariable(n);
		}
		System.out.println("invalid Token: " + n.toStringTree());
		throw new UnexpectedTokenException(n,
										   FORALL,
										   EXISTS,
										   LIMP,
										   LEQ,
										   LXOR,
										   LOR,
										   LAND,
										   EQ,
										   NE,
										   LT,
										   LE,
										   GT,
										   GE,
										   LNOT,
										   TRUE,
										   FALSE);
	}

	public Expression<Boolean> translateLogicalNegation(Tree n) throws ImpreciseRepresentationException {
		requireType(n, LNOT);

		Expression<Boolean> negated = translateBoolExpression(n.getChild(0));
		return new Negation(negated);
	}

	public Expression<Boolean> translateQuantifier(Tree n) throws ImpreciseRepresentationException {
		Quantifier q;
		switch (n.getType()) {
			case EXISTS:
				q = Quantifier.EXISTS;
				break;
			case FORALL:
				q = Quantifier.FORALL;
				break;
			default:
				throw new UnexpectedTokenException(n, FORALL, EXISTS);
		}
		List<? extends Variable<?>> vars = translateQuantifiedVarList(n.getChild(0));
		pushContext(vars);
		Expression<Boolean> body = translateBoolExpression(n.getChild(1));
		popContext();
		return new QuantifierExpression(q, vars, body);
	}

	public Expression<Boolean> translatePropositionalCompound(Tree n) throws ImpreciseRepresentationException {
		LogicalOperator lop;
		switch (n.getType()) {
			case LIMP:
				lop = LogicalOperator.IMPLY;
				break;
			case LEQ:
				lop = LogicalOperator.EQUIV;
				break;
			case LOR:
				lop = LogicalOperator.OR;
				break;
			case LXOR:
				lop = LogicalOperator.XOR;
				break;
			case LAND:
				lop = LogicalOperator.AND;
				break;
			default:
				throw new UnexpectedTokenException(n, LIMP, LEQ, LOR, LXOR, LAND);
		}

		Expression<Boolean> head = translateBoolExpression(n.getChild(0));

		int count = n.getChildCount();
		for (int i = 1; i < count; i++) {
			Expression<Boolean> next = translateBoolExpression(n.getChild(i));
			head = new PropositionalCompound(head, lop, next);
		}

		return head;
	}

	public Expression<Boolean> translateNumericComparison(Tree n) throws ImpreciseRepresentationException {
		NumericComparator cmp;
		switch (n.getType()) {
			case EQ:
				cmp = NumericComparator.EQ;
				break;
			case NE:
				cmp = NumericComparator.NE;
				break;
			case LT:
				cmp = NumericComparator.LT;
				break;
			case LE:
				cmp = NumericComparator.LE;
				break;
			case GT:
				cmp = NumericComparator.GT;
				break;
			case GE:
				cmp = NumericComparator.GE;
				break;
			default:
				throw new UnexpectedTokenException(n, EQ, NE, LT, LE, GT, GE);
		}

		Expression<?> left = translateArithmeticExpression(n.getChild(0));
		Expression<?> right = translateArithmeticExpression(n.getChild(1));

		return NumericBooleanExpression.create(left, cmp, right);
	}

	public Expression<?> translateArithmeticExpression(Tree n) throws ImpreciseRepresentationException {
		switch (n.getType()) {
			case BVOR:
			case BVXOR:
			case BVAND:
			case BVSHL:
			case BVSHR:
			case BVSHUR:
				return translateBitvectorOperator(n);
			case BVNEG:
				return translateBitvectorNegation(n);
			case ADD:
			case SUB:
			case MUL:
			case DIV:
			case REM:
				return translateNumericCompound(n);
			case UNARY_PLUS:
				return translateArithmeticExpression(n.getChild(0));
			case UNARY_MINUS:
				return translateUnaryMinus(n);
			case TYPE_CAST:
				return translateTypeCast(n);
			case ID:
			case PRIMEID:
			case QID:
				return translateVariable(n);
			case BYTE_LITERAL:
			case SHORT_LITERAL:
			case INT_LITERAL:
			case LONG_LITERAL:
			case FLOAT_LITERAL:
			case DOUBLE_LITERAL:
			case BIGINT_LITERAL:
			case BIGDECIMAL_LITERAL:
				return translateLiteral(n);
			case TRUE:
			case FALSE:
				return translateBoolExpression(n);
			default:
				throw new UnexpectedTokenException(n,
												   BVOR,
												   BVXOR,
												   BVAND,
												   BVSHL,
												   BVSHR,
												   BVSHUR,
												   BVNEG,
												   ADD,
												   SUB,
												   MUL,
												   DIV,
												   REM,
												   UNARY_PLUS,
												   UNARY_MINUS,
												   TYPE_CAST);
		}
	}

	public Expression<?> translateLiteral(Tree n) throws ImpreciseRepresentationException {
		Type<?> type = null;
		switch (n.getType()) {
			case BYTE_LITERAL:
				type = BuiltinTypes.SINT8;
				break;
			case SHORT_LITERAL:
				type = BuiltinTypes.SINT16;
				break;
			case INT_LITERAL:
				type = BuiltinTypes.SINT32;
				break;
			case LONG_LITERAL:
				type = BuiltinTypes.SINT64;
				break;
			case FLOAT_LITERAL:
				type = BuiltinTypes.FLOAT;
				break;
			case DOUBLE_LITERAL:
				type = BuiltinTypes.DOUBLE;
				break;
			case BIGINT_LITERAL:
				type = BuiltinTypes.INTEGER;
				break;
			case BIGDECIMAL_LITERAL:
				type = BuiltinTypes.DECIMAL;
				break;
			default:
				throw new UnexpectedTokenException(n,
												   BYTE_LITERAL,
												   SHORT_LITERAL,
												   INT_LITERAL,
												   LONG_LITERAL,
												   FLOAT_LITERAL,
												   DOUBLE_LITERAL,
												   BIGINT_LITERAL,
												   BIGDECIMAL_LITERAL);
		}

		String txt = n.getText();
		int lastIdx = txt.length() - 1;
		char last = txt.charAt(lastIdx);
		if (!Character.isDigit(last)) {
			txt = txt.substring(0, lastIdx);
		}

		return Constant.createParsed(type, txt);
	}

	public Expression<?> translateVariable(Tree n) {
		String id = translateIdentifier(n);

		Variable<?> var = current.lookup(id);

		if (var == null) {
			throw new UndeclaredVariableException(n);
		}

		return var;
	}

	public Expression<?> translateBitvectorOperator(Tree n) throws ImpreciseRepresentationException {
		BitvectorOperator op;
		switch (n.getType()) {
			case BVOR:
				op = BitvectorOperator.OR;
				break;
			case BVXOR:
				op = BitvectorOperator.XOR;
				break;
			case BVAND:
				op = BitvectorOperator.AND;
				break;
			case BVSHL:
				op = BitvectorOperator.SHIFTL;
				break;
			case BVSHR:
				op = BitvectorOperator.SHIFTR;
				break;
			case BVSHUR:
				op = BitvectorOperator.SHIFTUR;
				break;
			default:
				throw new UnexpectedTokenException(n, BVOR, BVXOR, BVAND, BVSHL, BVSHR, BVSHUR);
		}

		Expression<?> left = translateArithmeticExpression(n.getChild(0));
		Expression<?> right = translateArithmeticExpression(n.getChild(1));

		return BitvectorExpression.createCompatible(left, op, right, types);
	}

	public Expression<?> translateBitvectorNegation(Tree n) throws ImpreciseRepresentationException {
		requireType(n, BVNEG);

		Expression<?> negated = translateArithmeticExpression(n.getChild(0));

		return BitvectorNegation.create(negated);
	}

	public Expression<?> translateNumericCompound(Tree n) throws ImpreciseRepresentationException {
		NumericOperator op;
		switch (n.getType()) {
			case ADD:
				op = NumericOperator.PLUS;
				break;
			case SUB:
				op = NumericOperator.MINUS;
				break;
			case MUL:
				op = NumericOperator.MUL;
				break;
			case DIV:
				op = NumericOperator.DIV;
				break;
			case REM:
				op = NumericOperator.REM;
				break;
			default:
				throw new UnexpectedTokenException(n, ADD, SUB, MUL, DIV, REM);
		}

		Expression<?> left = translateArithmeticExpression(n.getChild(0));
		Expression<?> right = translateArithmeticExpression(n.getChild(1));

		return NumericCompound.createCompatible(left, op, right, types);
	}

	public Expression<?> translateUnaryMinus(Tree n) throws ImpreciseRepresentationException {
		requireType(n, UNARY_MINUS);

		Expression<?> negated = translateArithmeticExpression(n.getChild(0));

		return UnaryMinus.create(negated);
	}

	public Expression<?> translateTypeCast(Tree n) throws ImpreciseRepresentationException {
		requireType(n, TYPE_CAST);

		NumericType<?> toType = (NumericType<?>) translateType(n.getChild(0));
		Expression<?> fromExpr = translateArithmeticExpression(n);

		return CastExpression.create(fromExpr, toType);
	}

	public List<? extends Variable<?>> translateTypedVarList(Tree n) {
		requireType(n, TYPED_VAR_LIST);
		int count = n.getChildCount();

		List<Variable<?>> result = new ArrayList<Variable<?>>(count);

		for (int i = 0; i < count; i++) {
			Variable<?> var = translateTypedVar(n.getChild(i));
			result.add(var);
		}

		return result;
	}

	public List<? extends Variable<?>> translateQuantifiedVarList(Tree n) {
		requireType(n, QUANTIFIER_VAR_LIST);
		int count = n.getChildCount();

		List<Variable<?>> result = new ArrayList<>(count);

		for (int i = 0; i < count; i++) {
			Variable var;
			switch (n.getChild(i).getType()) {
				case QUANTIFIER_VAR:
					var = (Variable) translateQuantifierVariable(n.getChild(i));
					break;
				case TYPED_VAR:
					var = translateTypedVar(n.getChild(i));
					break;
				default:
					throw new UnexpectedTokenException(n, QUANTIFIER_VAR, TYPED_VAR);
			}
			result.add(var);
		}
		return result;
	}

	public Variable<?> translateQuantifierVariable(Tree n) {
		requireType(n, ExpressionParser.QUANTIFIER_VAR);
		String varName = translateIdentifier(n.getChild(0));
		Variable<?> var = current.lookup(varName);
		if (var == null) {
			throw new UndeclaredVariableException(n);
		}
		return var;
	}

	public Variable<?> translateTypedVar(Tree n) {
		requireType(n, ExpressionParser.TYPED_VAR);
		String varName = translateIdentifier(n.getChild(0));
		Type<?> type = translateType(n.getChild(1));
		return Variable.create(type, varName);
	}

	public String translateIdentifier(Tree n) {
		switch (n.getType()) {
			case ExpressionParser.ID:
			case ExpressionParser.PRIMEID:
				return n.getText();
			case ExpressionParser.QID:
				String txt = n.getText();
				// TODO : unescape quotes
				return txt.substring(1, txt.length() - 1);
		}
		throw new UnexpectedTokenException(n, ExpressionParser.ID, ExpressionParser.QID);
	}

	public Type<?> translateType(Tree n) {
		requireType(n, ExpressionParser.ID);
		String name = n.getText();
		Type<?> type = types.byName(name);
		if (type == null) {
			throw new UnknownTypeException(n);
		}
		return type;
	}


	private static void requireType(Tree n, int... expected) {
		int t = n.getType();
		for (int i = 0; i < expected.length; i++) {
			if (t == expected[i]) {
				return;
			}
		}
		throw new UnexpectedTokenException(n, expected);
	}


}
