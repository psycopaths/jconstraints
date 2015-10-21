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
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import gov.nasa.jpf.constraints.expressions.functions.math.UnaryDoubleFunction;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;

public class TanProperties implements FunctionProperties {

    public static final Function TAN_LOOKUP = new UnaryDoubleFunction("tan_lookup") {
        @Override
        protected double doEvaluate(double value) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    };

    public static final Function TAN_PI = new UnaryDoubleFunction("tan_pi") {
        @Override
        protected double doEvaluate(double value) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    };    
    
    private final int lookupSize;
    
    public TanProperties(int lookupSize) {
        this.lookupSize = lookupSize;
    }
    
    private Expression<Boolean> lookupTable() {
        double[] domain = interval(0 , 90.0, lookupSize);
        double[] values = new double[domain.length];
        for (int i=0; i<domain.length; i++) {
            domain[i] = Math.toRadians(domain[i]);
            values[i] = Math.tan(domain[i]);
        }

        return linearInterpolation(TAN_LOOKUP, domain, values);
    }
    
    private Expression<Boolean> tanPi() {
        Variable arg = doubleVar();                
        
        // pi * 1.5 <= arg <= pi * 2.0
        Expression<Boolean> ifCond = bounds(arg, Math.PI * 1.5, Math.PI * 2.0, false, false);
        Expression elseExpr = constant(0.0);
        Expression thenExpr = new UnaryMinus(fexpr(TAN_LOOKUP, minus(constant(Math.PI * 2.0), arg)));
        elseExpr = ite(ifCond, thenExpr, elseExpr);        
        
        // pi <= arg <= pi * 1.5
        ifCond = bounds(arg, Math.PI, Math.PI * 1.5, false, false);
        thenExpr = fexpr(TAN_LOOKUP, minus(arg, constant(Math.PI)));
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        
        // pi * 0.5 <= arg <= pi
        ifCond = bounds(arg, Math.PI * 0.5, Math.PI, false, false);
        thenExpr = fexpr(TAN_LOOKUP, new UnaryMinus(minus(constant(Math.PI), arg)));
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        
        // 0.0 <= arg <= pi * 0.5
        ifCond = bounds(arg, 0.0, Math.PI * 0.5, false, false);
        thenExpr = fexpr(TAN_LOOKUP, arg);
        
        return forall(eq(fexpr(TAN_PI, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);        
    }
    
    private Expression<Boolean> tan() {
        Variable arg = doubleVar();                
        Expression<Boolean> ifCond = gte(arg, constant(0.0));
        Expression thenExpr = fexpr(TAN_PI, arg);
        Expression elseExpr = new UnaryMinus(fexpr(TAN_PI, new UnaryMinus(arg)));        
        return forall(eq(fexpr(MathFunctions.TAN, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);                
    }
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        return new Expression[] {lookupTable(), tanPi(), tan()};        
    }

    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return new Expression[] {};
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return array(bounds(fargs[0], Math.PI * -2.0, Math.PI * 2.0, false, false));
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        throw new UnsupportedOperationException("Not supported yet."); 
    }

    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVale) {
        return array();
    }
    
}
