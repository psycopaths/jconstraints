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
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import gov.nasa.jpf.constraints.expressions.functions.math.UnaryDoubleFunction;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class SinProperties implements FunctionProperties {

    public static final Function SIN_LOOKUP = new UnaryDoubleFunction("sin_lookup") {
        @Override
        protected double doEvaluate(double value) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    };

    public static final Function SIN_PI = new UnaryDoubleFunction("sin_pi") {
        @Override
        protected double doEvaluate(double value) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    };    
    
    private final int lookupSize;
    
    public SinProperties(int lookupSize) {
        this.lookupSize = lookupSize;
    }
    
    private Expression<Boolean> lookupTable() {
        Variable x = var(BuiltinTypes.DOUBLE);
        IfThenElse ite = lookupTable(x);
        return linearInterpolation(SIN_LOOKUP, ite, x);
    }
        
    private IfThenElse lookupTable(Variable x) {
        double[] domain = interval(0 , 90.0, lookupSize);
        double[] values = new double[domain.length];
        for (int i=0; i<domain.length; i++) {
            domain[i] = Math.toRadians(domain[i]);
            values[i] = Math.sin(domain[i]);
        }

        return linearInterpolation(x, domain, values);
    }
    
    private Expression<Boolean> sinPi() {
        Variable arg = doubleVar();                
        
        // pi * 1.5 <= arg <= pi * 2.0
        Expression<Boolean> ifCond = bounds(arg, Math.PI * 1.5, Math.PI * 2.0, false, false);
        Expression elseExpr = constant(0.0);
        Expression thenExpr = new UnaryMinus(fexpr(SIN_LOOKUP, minus(constant(Math.PI * 2.0), arg)));
        elseExpr = ite(ifCond, thenExpr, elseExpr);        
        
        // pi <= arg <= pi * 1.5
        ifCond = bounds(arg, Math.PI, Math.PI * 1.5, false, false);
        thenExpr = new UnaryMinus(fexpr(SIN_LOOKUP, minus(arg, constant(Math.PI))));
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        
        // pi * 0.5 <= arg <= pi
        ifCond = bounds(arg, Math.PI * 0.5, Math.PI, false, false);
        thenExpr = fexpr(SIN_LOOKUP, minus(constant(Math.PI), arg));
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        
        // 0.0 <= arg <= pi * 0.5
        ifCond = bounds(arg, 0.0, Math.PI * 0.5, false, false);
        thenExpr = fexpr(SIN_LOOKUP, arg);
        
        return forall(eq(fexpr(SIN_PI, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);        
    }
    
    private Expression<Boolean> sin() {
        Variable arg = doubleVar();                
        Expression<Boolean> ifCond = gte(arg, constant(0.0));
        Expression thenExpr = fexpr(SIN_PI, arg);
        Expression elseExpr = new UnaryMinus(fexpr(SIN_PI, new UnaryMinus(arg)));        
        return forall(eq(fexpr(MathFunctions.SIN, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);                
    }
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        Expression<Boolean> lookup = lookupTable();
        Expression<Boolean> sin_pi = sinPi();
        Expression<Boolean> sin = sin();        
        return array(lookup, sin_pi, sin);
    }

    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return array(bounds(MathFunctions.SIN, constant(-1.0), constant(1.0), false));
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {        
        return array(bounds(fargs[0], Math.PI * -2.0, Math.PI * 2.0, false, false));
    }
    
    
    private Expression<Boolean> sinPi(Variable arg, Variable ret, Variable argL, Variable retL) {
        //Variable arg = doubleVar();                
        
        // pi * 1.5 <= arg <= pi * 2.0
        Expression<Boolean> ifCond = bounds(arg, Math.PI * 1.5, Math.PI * 2.0, false, false);        
        Expression thenExprArg = minus(constant(Math.PI * 2.0), arg);
        Expression thenExprRet = new UnaryMinus(retL);
        Expression elseExprRet = constant(0.0);
        Expression elseExprArg =  constant(0.0);                
        elseExprArg = ite(ifCond, thenExprArg, elseExprArg);
        elseExprRet = ite(ifCond, thenExprRet, elseExprRet);
        
        // pi <= arg <= pi * 1.5
        ifCond = bounds(arg, Math.PI, Math.PI * 1.5, false, false);
        thenExprArg = minus(arg, constant(Math.PI));
        thenExprRet = new UnaryMinus(retL);
        elseExprArg = ite(ifCond, thenExprArg, elseExprArg);
        elseExprRet = ite(ifCond, thenExprRet, elseExprRet);
        
        // pi * 0.5 <= arg <= pi
        ifCond = bounds(arg, Math.PI * 0.5, Math.PI, false, false);
        thenExprArg = minus(constant(Math.PI), arg);
        thenExprRet = retL;
        elseExprArg = ite(ifCond, thenExprArg, elseExprArg);
        elseExprRet = ite(ifCond, thenExprRet, elseExprRet);
        
        
        // 0.0 <= arg <= pi * 0.5
        ifCond = bounds(arg, 0.0, Math.PI * 0.5, false, false);
        thenExprArg = arg;
        thenExprRet = retL;
        
        return ExpressionUtil.and(
                eq(ret, ite(ifCond, thenExprRet, elseExprRet)), 
                eq(argL, ite(ifCond, thenExprArg, elseExprArg)));
    }
    
    private Expression<Boolean> sin(Expression arg, Variable ret, Variable argPi, Variable retPi) {
        Expression<Boolean> ifCond = gte(arg, constant(0.0));
        IfThenElse iteRet = ite(ifCond, retPi, new UnaryMinus<>(retPi));        
        IfThenElse iteArg = ite(ifCond, arg, new UnaryMinus<>(arg));
        return ExpressionUtil.and(eq(ret, iteRet), eq(argPi, iteArg));        
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        Variable lArg = var(BuiltinTypes.DOUBLE);
        Variable lRet = var(BuiltinTypes.DOUBLE);
        Variable piArg = var(BuiltinTypes.DOUBLE);
        Variable piRet = var(BuiltinTypes.DOUBLE);
        
        return array( 
                eq(lRet, lookupTable(lArg)), 
                sinPi(piArg, piRet, lArg, lRet),
                sin(fargs[0], retValue, piArg, piRet)         
        );
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVal) {
        return array(bounds(retVal, -1.0, 1.0, false, false));        
    }        
}
