/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * Copyright (C) 2015, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * <p>Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p> Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com)
 * We license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.solvers.nativez3;

import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FPNum;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import gov.nasa.jpf.constraints.util.TypeUtil;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class NativeZ3SolverContext extends SolverContext {

	private static final Logger logger = Logger.getLogger("constraints");

	private final Deque<NativeZ3ExpressionGenerator> generatorStack = new ArrayDeque<>();
	private final Deque<Expression<Boolean>> expressionStack = new ArrayDeque<>();
	private final Deque<Map<String, Variable<?>>> freeVarsStack = new ArrayDeque<>();

	private Solver solver;

	private final Pattern bytePattern = Pattern
			.compile("(?:[^\\\\]|^)(?<toBeReplaced>\\\\x(?<digits>[0-9a-f]{2}))");

	public NativeZ3SolverContext(final Solver solver,
			final NativeZ3ExpressionGenerator rootGenerator) {
		this.solver = solver;
		this.generatorStack.push(rootGenerator);
		this.expressionStack.push(ExpressionUtil.TRUE);
		this.freeVarsStack.push(new HashMap<String, Variable<?>>());
	}

	@Override
	public void push() {
		try {
			solver.push();
			final Map<String, Variable<?>> fvMap = freeVarsStack.peek();
			generatorStack.push(generatorStack.peek().createChild());
			freeVarsStack.push(new HashMap<String, Variable<?>>(fvMap));
			expressionStack.push(ExpressionUtil.TRUE);
		}
		catch (final Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public void pop(final int n) {
		for (int i = 0; i < n; i++) {
			final NativeZ3ExpressionGenerator gen = generatorStack.pop();
			gen.dispose();
			freeVarsStack.pop();
			expressionStack.pop();
		}
		try {
			solver.pop(n);
		}
		catch (final Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	public Result approximate(final Valuation val) {
		logger.finer("Solving ...");
		try {
			final Status status = solver.check();
			if (status != Status.SATISFIABLE || val == null) {
				logger.finer("Not satisfiable: " + status);

				if (status == Status.UNSATISFIABLE) {
					logger.finest("unsat core: ");
					for (final Expr e : solver.getUnsatCore()) {
						logger.finest("  " + e.getSExpr());
					}
				}

				return translateStatus(status);
			}

			Model model = solver.getModel();
			try {
				if (logger.isLoggable(Level.FINE)) {
					final String modelText = model.toString().replace("\n", ", ").trim();
					logger.fine(modelText);
				}

				final NativeZ3ExpressionGenerator gen = generatorStack.peek();
				if (gen.isTainted(model)) {
					//          model.dispose();
					logger.info("Model is tainted, rechecking ...");
					model = gen.recheckUntainted();
					if (model == null) {
						return Result.DONT_KNOW;
					}
				}

				// FIXME mi: using origVars here fixes the issue that variables occuring only in the
				//           scope of quantifiers are part of the valuation. Might it break something
				//           else?
				final long max = model.getNumConsts();
				final FuncDecl[] decls = model.getConstDecls();
				try {
					try {
						val.putAll(parseModel(model, true));
					}
					catch (ImpreciseRepresentationException e) {
						throw new RuntimeException("Imprecise Representation");
					}

				}
				finally {
					for (int i = 0; i < decls.length; i++) {
						//            decls[i].dispose();
					}
				}


			}
			finally {
				//        model.dispose();
			}

			logger.finer("Satisfiable, valuation " + val);
			return Result.SAT;
		}
		catch (final Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	@Override
	public Result solve(final Valuation val) {
		logger.finer("Solving ...");
		try {
			final Status status = solver.check();
			if (status != Status.SATISFIABLE || val == null) {
				logger.finer("Not satisfiable: " + status);

				if (status == Status.UNSATISFIABLE) {
					logger.finest("unsat core: ");
					for (final Expr e : solver.getUnsatCore()) {
						logger.finest("  " + e.getSExpr());
					}
				}

				return translateStatus(status);
			}

			Model model = solver.getModel();
			try {
				if (logger.isLoggable(Level.FINE)) {
					final String modelText = model.toString().replace("\n", ", ").trim();
					logger.fine(modelText);
				}

				final NativeZ3ExpressionGenerator gen = generatorStack.peek();
				if (gen.isTainted(model)) {
					//          model.dispose();
					logger.info("Model is tainted, rechecking ...");
					model = gen.recheckUntainted();
					if (model == null) {
						return Result.DONT_KNOW;
					}
				}

				// FIXME mi: using origVars here fixes the issue that variables occuring only in the
				//           scope of quantifiers are part of the valuation. Might it break something
				//           else?
				final long max = model.getNumConsts();
				final FuncDecl[] decls = model.getConstDecls();
				try {
					try {
						val.putAll(parseModel(model));
					}
					catch (ImpreciseRepresentationException e) {
						Valuation testVal = new Valuation();
						testVal.putAll(val);
						try {
							testVal.putAll(parseModel(model, true));
							if (validateExpressionStack(testVal)) {
								val.putAll(testVal, true);
							} else {
								throw new ImpreciseRepresentationException("Cannot fix the imprecise " + "Representation");
							}
						}
						catch (ImpreciseRepresentationException e2) {
							throw new RuntimeException("Imprecise Representation");
						}
					}

				}
				finally {
					for (int i = 0; i < decls.length; i++) {
						//            decls[i].dispose();
					}
				}


			}
			finally {
				//        model.dispose();
			}

			logger.finer("Satisfiable, valuation " + val);
			return Result.SAT;
		}
		catch (final Z3Exception ex) {
			throw new RuntimeException(ex);
		}
	}

	private boolean validateExpressionStack(Valuation val) {
		Expression<Boolean> combined = ExpressionUtil.and(expressionStack);
		return combined.evaluate(val);
	}

	private Valuation parseModel(final Model model) throws ImpreciseRepresentationException {
		return parseModel(model, false);
	}

	private Valuation parseModel(final Model model, boolean unsafe) throws ImpreciseRepresentationException {
		Valuation val = new Valuation();

		final Map<String, Variable<?>> freeVars = new HashMap<>(freeVarsStack.peek());
		final long max = model.getNumConsts();
		final FuncDecl[] decls = model.getConstDecls();
		for (int i = 0; i < max; i++) {
			final FuncDecl decl = decls[i];
			Symbol sym = null;
			String text = null;
			try {
				sym = decl.getName();
				text = sym.toString().trim();
			}
			finally {
				//              sym.dispose();
			}

			final Variable<?> v = freeVars.get(text);
			if (v == null) {
				continue;
			}
			freeVars.remove(text);

			final AST res = model.getConstInterp(decl);
			final String value = res.toString().trim();
			if (res instanceof FPNum) {
				FPNum resFP = (FPNum) res;
				long rep = resFP.getSignificandUInt64();
				Double d = Double.longBitsToDouble(rep);
				if (v.getType().equals(BuiltinTypes.DOUBLE)) {
					val.setValue((Variable<Double>) v, d);
					continue;
				} else if (v.getType().equals(BuiltinTypes.FLOAT)) {
					val.setValue((Variable<Float>) v, d.floatValue());
					continue;
				} else {
					throw new IllegalArgumentException("Cannot parse the FP value");
				}
			}
			if (TypeUtil.isRealSort(v) && value.contains("/")) {
				final String[] split = value.split("/");
				final BigDecimal nom = new BigDecimal(split[0].trim());
				final BigDecimal den = new BigDecimal(split[1].trim());
				final BigDecimal quot = nom.divide(den, 10, RoundingMode.FLOOR);
				if (unsafe) {
					val.setUnsafeParsedValue(v, quot.toPlainString());
				} else {
					val.setParsedValue(v, quot.toPlainString());
				}
			} else if (TypeUtil.isRealSort(v)) {
				//Z3 might print a question mark at the end of the number, if it is an inexact
				// representation
				// and Z3 is aware of the inexact representation. Java cannot handle the question
				// mark.
				//TODO: How to do this right.
				// Z3 return originally: (root-obj (+ (^ x 2) (- 2)) 2) for root of 2.
				String tmpValue = value.replace("?", "");
				if (unsafe) {
					val.setUnsafeParsedValue(v, tmpValue);
				} else {
					val.setParsedValue(v, tmpValue);
				}
			} else if (v.getType().equals(BuiltinTypes.STRING)) {
				String sValue = value.replace("\"", "");
				Matcher m = bytePattern.matcher(sValue);
				while (m.find()) {
					String group = m.group("digits");
					char c = (char) Integer.parseInt(group, 16);
					sValue = sValue.replace(m.group("toBeReplaced"), new String(new char[]{c}));
				}
				sValue = sValue.replaceAll(Pattern.quote("\\\\"), "\\\\");
				val.setValue((Variable<String>) v, sValue);
			} else {
				if (unsafe) {
					val.setUnsafeParsedValue(v, value);
				} else {
					val.setParsedValue(v, value);
				}
			}
		}
		for (final Variable<?> r : freeVars.values()) {
			val.setDefaultValue(r);
		}
		return val;
	}

	@Override
	public void dispose() {
		while (!generatorStack.isEmpty()) {
			generatorStack.pop().dispose();
		}
		freeVarsStack.clear();

		try {
			//      solver.dispose();
		}
		catch (final Z3Exception ex) {
		}
		finally {
			solver = null;
		}
	}

	@Override
	protected void finalize() throws Throwable {
		super.finalize();

		if (solver != null) {
			dispose();
		}
	}

	@Override
	public void add(final List<Expression<Boolean>> expressions) {
		final BoolExpr[] exprs = new BoolExpr[expressions.size()];

		final NativeZ3ExpressionGenerator gen = generatorStack.peek();

		final Map<String, Variable<?>> fvMap = freeVarsStack.peek();

		Expression<Boolean> currentExpression = expressionStack.pop();
		expressionStack.push(ExpressionUtil.and(currentExpression, ExpressionUtil.and(expressions)));

		int i = 0;
		try {
			for (final Expression<Boolean> ex : expressions) {
				//logger.finer("Checking " + ex);
				exprs[i++] = gen.generateAssertion(ex);
				final Set<Variable<?>> fvs = ExpressionUtil.freeVariables(ex);
				for (final Variable<?> v : fvs) {
					fvMap.put(v.getName(), v);
				}
			}

			solver.add(exprs);
		}
		catch (final Z3Exception ex) {
			throw new RuntimeException(ex);
		}
		finally {
			// !!! This is a very important corner case. Sometimes, the expression
			// might just be a single boolean variable, WHICH MAY BE PROTECTED!
			gen.safeDispose(exprs);
		}
	}

	private static Result translateStatus(final Status status) {
		switch (status) {
			case SATISFIABLE:
				return Result.SAT;
			case UNSATISFIABLE:
				return Result.UNSAT;
			default: // case UNKNOWN:
				return Result.DONT_KNOW;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		try {
			for (final BoolExpr e : this.solver.getAssertions()) {
				sb.append(e.getSExpr()).append("\n");
			}
		}
		catch (final Z3Exception ex) {
			sb.append("Error: ").append(ex.getMessage());
		}
		return sb.toString();
	}
}
