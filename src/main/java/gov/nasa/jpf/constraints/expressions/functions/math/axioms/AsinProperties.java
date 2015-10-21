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

public class AsinProperties implements FunctionProperties {

    public static final Function ASIN_LOOKUP = new UnaryDoubleFunction("asin_lookup") {
        @Override
        protected double doEvaluate(double value) {
            throw new UnsupportedOperationException("Not supported yet.");
        }
    };
 
    private final int lookupSize;
    
    public AsinProperties(int lookupSize) {
        this.lookupSize = lookupSize;
    }
    
    private Expression<Boolean> lookupTable() {
        Variable x = var(BuiltinTypes.DOUBLE);
        IfThenElse ite = lookupTable(x);
        return linearInterpolation(ASIN_LOOKUP, ite, x);
    }
    
    private IfThenElse lookupTable(Expression x) {
        double[] domain = interval(0.0 , 1.0, lookupSize);
        double[] values = new double[domain.length];
        for (int i=0; i<domain.length; i++) {
            values[i] = Math.asin(domain[i]);
            //System.out.println(values[i]);
        }

        values[values.length-1] = Math.asin(0.99999999999999);        
        return linearInterpolation(x, domain, values);
    }
    
    private Expression<Boolean> asin() {
        Variable arg = doubleVar();                
        Expression<Boolean> ifCond = gte(arg, constant(0.0));
        Expression thenExpr = fexpr(ASIN_LOOKUP, arg);
        Expression elseExpr = new UnaryMinus(fexpr(ASIN_LOOKUP, new UnaryMinus(arg)));        
        return forall(eq(fexpr(MathFunctions.ASIN, arg), 
                ite(ifCond, thenExpr, elseExpr)), arg);                
    }
    
    private Expression<Boolean> asin(Expression arg, Variable ret, Variable argL, Variable retL) {
        Expression<Boolean> ifCond = gte(arg, constant(0.0));
        Expression thenExprArg = arg;
        Expression thenExprRet = retL; 
        Expression elseExprArg = new UnaryMinus(arg);        
        Expression elseExprRet = new UnaryMinus(retL);
        
        return ExpressionUtil.and(
                eq(argL, ite(ifCond, thenExprArg, elseExprArg)),
                eq(ret, ite(ifCond, thenExprRet, elseExprRet))
        );
    }
        
    @Override
    public Expression<Boolean>[] getDefinition() {
        Expression<Boolean> lookup = lookupTable();
        Expression<Boolean> asin = asin();        
        return array(lookup, asin);
    }    


    @Override
    public Expression<Boolean>[] getRangeBounds() {
        // FIXME: the computed value for 1.0 is not within these bounds!!!
        return array(bounds(MathFunctions.ASIN, constant(-0.5 * Math.PI), constant(0.5 * Math.PI), false));
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return array(bounds(fargs[0], -1.0, 1.0, false, false));
    }

    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        Variable lArg = var(BuiltinTypes.DOUBLE);
        Variable lRet = var(BuiltinTypes.DOUBLE);        
        
        return array( 
                eq(lRet, lookupTable(lArg)), 
                asin(fargs[0], retValue, lArg, lRet)
        );
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVal) {
        return array(bounds(retVal, -0.5 * Math.PI, 0.5 * Math.PI, false, false));
    }    
    
}
