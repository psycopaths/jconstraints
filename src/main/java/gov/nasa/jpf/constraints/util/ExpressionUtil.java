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

package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Objects;
import java.util.Set;

import com.google.common.base.Function;
import com.google.common.base.Predicate;

public class ExpressionUtil {
  
  public static final Constant<Boolean> FALSE = Constant.create(BuiltinTypes.BOOL, Boolean.FALSE);
  public static final Constant<Boolean> TRUE = Constant.create(BuiltinTypes.BOOL, Boolean.TRUE);
  
  public static Constant<Boolean> boolConst(boolean val) {
    return val ? TRUE : FALSE;
  }
  
  
  public static boolean isConstant(Expression<?> expr, Object value) {
    if(!(expr instanceof Constant))
      return false;
    Constant<?> cnst = (Constant<?>)expr;
    return Objects.equals(cnst.getValue(), value);
  }
  
  public static boolean isBoolConst(Expression<?> expr, boolean value) {
    return isConstant(expr, Boolean.valueOf(value));
  }
  
  public static boolean isTrue(Expression<?> expr) {
    return isBoolConst(expr, true);
  }
  
  public static boolean isFalse(Expression<?> expr) {
    return isBoolConst(expr, false); 
  }

  
  public static boolean containsVars(Expression<?> e) {
    return ContainsVarsVisitor.getInstance().apply(e);
  }
  
  public static <E> Expression<E> simplify(Expression<E> e) {
    return ExpressionSimplificationVisitor.getInstance().simplify(e);
  }
  
  
  public static <E> Expression<E> stripPrefix(Expression<E> e, String prefix) {
    return StripPrefixVisitor.INSTANCE.apply(e, prefix);
  }
  
  public static <E> Expression<E> addPrefix(Expression<E> e, String prefix) {
    return AddPrefixVisitor.INSTANCE.apply(e, prefix);
  }
  
  public static Set<Variable<?>> freeVariables(Expression<?> e) {
    Set<Variable<?>> vars = new HashSet<Variable<?>>();
    e.collectFreeVariables(vars);
    return vars;
  }

  public static Valuation stripPrefix(Valuation v, String prefix) {
    Valuation ret = new Valuation();
    for(ValuationEntry<?> e : v) 
      stripEntryPrefix(e, prefix, ret);
    return ret;
  }
  
  private static <E> void stripEntryPrefix(ValuationEntry<E> entry, String prefix, Valuation target) {
    Variable<E> var = entry.getVariable();
    String name = var.getName();
    if(name.startsWith(prefix))
      var = Variable.create(var.getType(), name.substring(prefix.length()));
    target.setValue(var, entry.getValue());
  }
  
  public static Expression<Boolean> combine(LogicalOperator op, Expression<Boolean> def, Iterable<? extends Expression<Boolean>> expressions) {
    Iterator<? extends Expression<Boolean>> it = expressions.iterator();
    
    
    if(!it.hasNext())
      return def;
    
    Expression<Boolean> curr = it.next();

    while(it.hasNext()) {
      Expression<Boolean> next = it.next();
      curr = new PropositionalCompound(curr, op, next);
    }
    
    return curr;
  }
  
  @SafeVarargs
  public static Expression<Boolean> or(Expression<Boolean> ...expressions) {
    return or(Arrays.asList(expressions));
  }
  
  public static Expression<Boolean> or(Iterable<? extends Expression<Boolean>> expressions) {
    return combine(LogicalOperator.OR, FALSE, expressions);
  }
  
  @SafeVarargs
  public static Expression<Boolean> and(Expression<Boolean> ...expressions) {
    return and(Arrays.asList(expressions));
  }
  
  public static Expression<Boolean> and(Iterable<? extends Expression<Boolean>> expressions) {
    return combine(LogicalOperator.AND, TRUE, expressions);
  }
  
  public static <T> Expression<T> restrict(Expression<T> expr, Predicate<? super Variable<?>> pred) {
    return ExpressionRestrictionVisitor.getInstance().apply(expr, pred);
  }
  
  public static <T> Expression<T> transformVars(Expression<T> expr, Function<? super Variable<?>,? extends Expression<?>> transform) {
    return TransformVarVisitor.getInstance().apply(expr, transform);
  }
  
  public static <T> Expression<T> renameVars(Expression<T> expr, Function<String,String> rename) {
    return RenameVarVisitor.getInstance().apply(expr, rename);
  }
  
  
  public static String toParseableString(Expression<?> expression) {
    Set<Variable<?>> freeVars = freeVariables(expression);
    
    if(freeVars.isEmpty())
      return expression.toString();
    
    StringBuilder sb = new StringBuilder();
    
    sb.append("declare ");
    
    try {
      boolean first = true;
      for(Variable<?> var : freeVars) {
        if(first)
          first = false;
        else
          sb.append(", ");
        var.printTyped(sb);
      }
      sb.append(" in ");
      expression.print(sb);
      
      return sb.toString();
    }
    catch(IOException ex) {
      throw new RuntimeException("Unexpected IOException while writing to a StringBuilder");
    }
  }
  
  
  public static Expression<Boolean> valuationToExpression(Valuation val) {
    Expression<Boolean> result = null;
    for(ValuationEntry<?> e : val) {
      result = addValuationEntryExpression(e, result);
    }
    return result;
  }
  
  private static <T> Expression<Boolean> addValuationEntryExpression(ValuationEntry<T> e, Expression<Boolean> expr) {
    Variable<T> var = e.getVariable();
    Type<T> type = var.getType();
    T value = e.getValue();
    Expression<Boolean> newExpr;
    if(BuiltinTypes.BOOL.equals(type)) {
      Expression<Boolean> bvar = var.as(BuiltinTypes.BOOL);
      if((Boolean)value) {
        newExpr = bvar;
      }
      else {
        newExpr = new Negation(bvar);
      }
    }
    else {
      Constant<T> cnst = Constant.create(type, value);
      newExpr = new NumericBooleanExpression(var, NumericComparator.EQ, cnst);
    }
    return (expr == null) ? newExpr : ExpressionUtil.and(newExpr, expr);
  }
  
  public static int nestingDepth(Expression<?> expr) {
    return NestingDepthVisitor.getInstance().apply(expr);
  }
  
  public static Valuation combineValuations(Iterable<? extends Valuation> vals) {
    Valuation ret = new Valuation();
    
    for(Valuation v : vals) {
      ret.putAll(v);
    }
    
    return ret;
  }
  
  public static Valuation combineValuations(Valuation ...vals) {
    return combineValuations(Arrays.asList(vals));
  }
  
  public static <T> Expression<T> partialEvaluate(Expression<T> expr, Valuation val) {
    return simplify(partialEvaluate(expr, val));
  }
  
  
  // LEGACY API
  
  @Deprecated
  @SuppressWarnings({"rawtypes","unchecked"})
  public static Set<Variable> getVariables(Expression e) {
    return (Set<Variable>)(Set)freeVariables(e); // This may not look like it's safe, but it is..
  }
  
  @Deprecated
  public static Expression<Boolean> combine(Iterable<? extends Expression<Boolean>> expressions, LogicalOperator op) {
    return combine(op, null, expressions);
  }
}
