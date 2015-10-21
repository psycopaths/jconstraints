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
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;

public class CosProperties implements FunctionProperties {

    private final SinProperties sin;

    public CosProperties(SinProperties sin) {
        this.sin = sin;
    }
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        Variable arg = doubleVar();                
        
        // pi * -2.0 <= arg <= pi * 1.5
        Expression<Boolean> ifCond = bounds(arg, Math.PI * -2.0, Math.PI * 1.5, false, false);        
        Expression thenExpr = fexpr(MathFunctions.SIN, plus(constant(Math.PI * 0.5), arg));
        Expression elseExpr = constant(0.0);
        
        // pi * 1.5 <= arg <= pi * 2.0
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        ifCond = bounds(arg, Math.PI * 1.5, Math.PI * 2.0, false, false);
        thenExpr = new UnaryMinus(fexpr(MathFunctions.SIN, minus(arg, constant(Math.PI * 0.5))));
             
        Expression<Boolean> cos = forall(eq(fexpr(MathFunctions.COS, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);        
        return array(cos);
    }

    private Expression<Boolean> cos(Expression arg, Variable ret, Variable sinArg, Variable sinRet) {
        
        // pi * -2.0 <= arg <= pi * 1.5
        Expression<Boolean> ifCond = bounds(arg, Math.PI * -2.0, Math.PI * 1.5, false, false);        
        
        Expression thenExprArg = plus(constant(Math.PI * 0.5), arg);
        Expression thenExprRet = sinRet;        
        Expression elseExprArg = constant(0.0);
        Expression elseExprRet = constant(0.0);
        
        elseExprArg = ite(ifCond, thenExprArg, elseExprArg);
        elseExprRet = ite(ifCond, thenExprRet, elseExprRet);

        ifCond = bounds(arg, Math.PI * 1.5, Math.PI * 2.0, false, false);
        thenExprArg = minus(arg, constant(Math.PI * 0.5));
        thenExprRet = new UnaryMinus(sinRet);
        
        return ExpressionUtil.and(
                eq(sinArg, ite(ifCond, thenExprArg, elseExprArg)),
                eq(ret, ite(ifCond, thenExprRet, elseExprRet))
        );
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return array(bounds(MathFunctions.COS, constant(-1.0), constant(1.0), false));
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return array(bounds(fargs[0], Math.PI * -2.0, Math.PI * 2.0, false, false));
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        Variable sinArg = var(BuiltinTypes.DOUBLE);
        Variable sinRet = var(BuiltinTypes.DOUBLE);
                
        Expression<Boolean>[] sinDefs = sin.getDefinition(sinRet, sinArg);
        Expression<Boolean>[] defs = new Expression[sinDefs.length+1];        
        defs[0] = cos(fargs[0], retValue, sinArg, sinRet);
        System.arraycopy(sinDefs, 0, defs, 1, sinDefs.length);
        
        return defs;
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVal) {
        return array(bounds(retVal, -1.0, 1.0, false, false));
    }    
    
}
