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
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;

public class PowProperties implements FunctionProperties {

    private Expression<Boolean> pow() {
        Variable base = doubleVar();                
        Variable exp = doubleVar();                
 
        Expression thenExpr = mul(base, base);
        Expression elseExpr = constant(-1.0);
        Expression<Boolean> ifCond = eq(exp, constant(2.0));
        
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        ifCond = eq(exp, constant(1.0));
        thenExpr = base;

        elseExpr = ite(ifCond, thenExpr, elseExpr);
        ifCond = eq(exp, constant(0.0));
        thenExpr = constant(1.0);
        
        return forall(eq(fexpr(MathFunctions.POW, base, exp) , ite(ifCond, thenExpr, elseExpr)), base, exp);
    }
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        return array(pow());
    }

    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return new Expression[] {};
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return new Expression[] {};
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        throw new UnsupportedOperationException("Not supported yet."); 
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVale) {
        throw new UnsupportedOperationException("Not supported yet."); 
    }    
    
}
