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

package gov.nasa.jpf.constraints.expressions.functions.math.axioms;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.Quantifier;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import static gov.nasa.jpf.constraints.util.ExpressionUtil.and;
import java.util.Arrays;

public class PropertyBuilder {
 
    private PropertyBuilder() {        
    }
    
    /* ***************************************************************************
     *
     * CONSTANTS
     *
     */
//    final static Constant ZERO = Constant.create(BuiltinTypes.DOUBLE, 0.0);
//    final static Constant ONE = Constant.create(BuiltinTypes.DOUBLE, 1.0);
//    final static Constant MINUS_ONE = Constant.create(BuiltinTypes.DOUBLE, -1.0);
//
//    final static Constant MINUS_PI_0_5 = Constant.create(BuiltinTypes.DOUBLE, Math.PI / -2.0);
//    final static Constant PI_0_5 = Constant.create(BuiltinTypes.DOUBLE, Math.PI / 2.0);
//    final static Constant PI = Constant.create(BuiltinTypes.DOUBLE, Math.PI);
//    final static Constant PI_1_5 = Constant.create(BuiltinTypes.DOUBLE, Math.PI * 1.5);
//    final static Constant PI_2_0 = Constant.create(BuiltinTypes.DOUBLE, Math.PI * 2.0);
//
//    final static Constant E = Constant.create(BuiltinTypes.DOUBLE, Math.E);

    /* ***************************************************************************
     *
     * LINEAR INTERPOLATION
     *
     */
    public static QuantifierExpression linearInterpolation(
            Function func, double[] dVals, double[] fVals) {

        assert dVals.length == fVals.length;
        assert dVals.length > 2;

        Variable x = var(BuiltinTypes.DOUBLE);
        FunctionExpression fe = fexpr(func, x);
        IfThenElse ite = linearInterpolation(x, dVals, fVals);
        Expression<Boolean> equal = eq(fe, ite);
        return forall(equal, x);
    }

    public static QuantifierExpression linearInterpolation(
            Function func, IfThenElse ite, Variable x) {

        FunctionExpression fe = fexpr(func, x);
        Expression<Boolean> equal = eq(fe, ite);
        return forall(equal, x);
    }
    
    public static IfThenElse linearInterpolation(
            Expression x, double[] dVals, double[] fVals) {
        
        Expression[] itp = new Expression[dVals.length - 1];
        for (int i = 0; i < itp.length; i++) {
            itp[i] = interpolate(x, fVals[i], fVals[i + 1], dVals[i], dVals[i + 1]);
        }

        IfThenElse ite = ite(bounds(x, dVals[dVals.length - 3], dVals[dVals.length - 2], false, false),
                itp[itp.length - 2], itp[itp.length - 1]);

        for (int i = 3; i < dVals.length; i++) {

            ite = ite(bounds(x, dVals[dVals.length - i - 1], dVals[dVals.length - i], false, false),
                    itp[itp.length - i], ite);
        }

        return ite; 
    }
    
    public static Expression interpolate(
            Expression x, double min, double max, double lower, double upper) {

        Constant minC = new Constant(BuiltinTypes.DOUBLE, min);
        Constant lowerC = new Constant(BuiltinTypes.DOUBLE, lower);
        
        Constant ratio = new Constant(BuiltinTypes.DOUBLE,  (max - min) / (upper - lower));
        return plus(minC, mul(ratio, minus(x, lowerC)));
    }       
    
    /* ***************************************************************************
     *
     * FUNCTIONS
     *
     */

    public static Expression<Boolean> bounds(Function func, Constant lower, Constant upper, boolean open) {
        Variable i[] = new Variable[func.getArity()];
        for (int j=0; j<i.length; j++) {
            i[j] = var(BuiltinTypes.DOUBLE);
        }
        FunctionExpression fe = fexpr(func, i);
        Expression<Boolean> lBound = open ? lt(lower, fe) : lte(lower, fe);
        Expression<Boolean> uBound = open ? gt(upper, fe) : gte(upper, fe);
        return forall(and(lBound, uBound), i);
    }

    public static Expression<Boolean> bounds(Expression x, double lower, double upper, boolean openLower, boolean openUpper) {
        Constant cl = new Constant(BuiltinTypes.DOUBLE, lower);
        Constant cu = new Constant(BuiltinTypes.DOUBLE, upper);

        Expression<Boolean> lBound = openLower ? lt(cl, x) : lte(cl, x);
        Expression<Boolean> uBound = openUpper ? lt(x, cu) : lte(x, cu);
        return and(lBound, uBound);
    }

    public static Expression<Boolean> lbound(Function func, Constant lower, boolean open) {
        Variable i = var(BuiltinTypes.DOUBLE);
        FunctionExpression fe = fexpr(func, i);
        Expression<Boolean> lBound = open ? lt(lower, fe) : lte(lower, fe);
        return forall(lBound, i);
    }    
    
    public static Expression<Boolean> ubound(Function func, Constant upper, boolean open) {
        Variable i = var(BuiltinTypes.DOUBLE);
        FunctionExpression fe = fexpr(func, i);
        Expression<Boolean> lBound = open ? gt(upper, fe) : gte(upper, fe);
        return forall(lBound, i);
    }  
    
    /* ***************************************************************************
     *
     * BASIC HELPERS
     *
     */
    public static FunctionExpression fexpr(Function f, Expression... args) {
        return new FunctionExpression(f, args);
    }

    public static <T extends Number> NumericBooleanExpression gt(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.GT, right);
    }

    public static <T extends Number> NumericBooleanExpression gte(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.GE, right);
    }

    public static <T extends Number> NumericBooleanExpression lt(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.LT, right);
    }

    public static <T extends Number> NumericBooleanExpression lte(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.LE, right);
    }

    public static <T extends Number> NumericBooleanExpression eq(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.EQ, right);
    }

    public static <T extends Number> NumericBooleanExpression neq(
            Expression<T> left, Expression<T> right) {
        return nbe(left, NumericComparator.NE, right);
    }

    public static QuantifierExpression forall(Expression<Boolean> expr, Variable<?>... vars) {
        return new QuantifierExpression(Quantifier.FORALL, Arrays.asList(vars), expr);
    }

    public static PropositionalCompound follows(Expression<Boolean> ante, Expression<Boolean> claim) {
        return new PropositionalCompound(ante, LogicalOperator.IMPLY, claim);
    }

    public static <T extends Number> NumericBooleanExpression nbe(
            Expression<T> left, NumericComparator c, Expression<T> right) {
        return new NumericBooleanExpression(left, c, right);
    }


    public static <E> IfThenElse<E> ite(Expression<Boolean> ifCond, Expression<E> thenExpr, Expression<E> elseExpr) {
        return new IfThenElse<>(ifCond, thenExpr, elseExpr);
    }

    public static <E> NumericCompound plus(Expression<E> left, Expression<E> right) {
        return new NumericCompound<>(left, NumericOperator.PLUS, right);
    }

    public static <E> NumericCompound minus(Expression<E> left, Expression<E> right) {
        return new NumericCompound<>(left, NumericOperator.MINUS, right);
    }

    public static <E> NumericCompound mul(Expression<E> left, Expression<E> right) {
        return new NumericCompound<>(left, NumericOperator.MUL, right);
    }

    public static <E> NumericCompound div(Expression<E> left, Expression<E> right) {
        return new NumericCompound<>(left, NumericOperator.DIV, right);
    }

    
    /* ***************************************************************************
     *
     * TERMINALS
     *
     */

    private static int id = 0;
    
    public static synchronized Variable<?> var(Type t) {
        return new Variable(t, "__axiom_" + id++);
    }    

    public static Variable<?> doubleVar() {
        return var(BuiltinTypes.DOUBLE);
    }    

    public static Constant constant(double val) {
        return new Constant(BuiltinTypes.DOUBLE, val);
    }     

    /* ***************************************************************************
     *
     * INTERVALS
     *
     */
    
    public static double[] interval(double min, double max, int elements) {
        double[] d = new double[elements];
        double width = max - min;
        double step = width / ((double) (elements - 1));
        double val = min;
        for (int i=0; i<elements; i++) {
            d[i] = val;
            val += step;
        }
        return d;
    }
    
    /* ***************************************************************************
     *
     * OTHER
     *
     */
    
    public static Expression<Boolean>[] array(Expression<Boolean> ... args) {
        return args;
    }
}
