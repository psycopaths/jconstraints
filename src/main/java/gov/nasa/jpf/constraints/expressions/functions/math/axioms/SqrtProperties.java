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
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public class SqrtProperties implements FunctionProperties {

    private final int lookupSize;
    
    public SqrtProperties(int lookupSize) {
        this.lookupSize = lookupSize;
    }
    
    private Expression<Boolean> sqrt() {
        Variable x = var(BuiltinTypes.DOUBLE);
        IfThenElse ite = lookupTable(x);
        return linearInterpolation(MathFunctions.SQRT, ite, x);
    }
    
    private IfThenElse lookupTable(Expression x) {        
        double[] domain = new double[lookupSize* 2 + 1];
        domain[lookupSize] = 1.0;
        for (int i=1; i<=lookupSize; i++) {
            domain[lookupSize + i] = 2.0 * domain[lookupSize + i - 1];
            domain[lookupSize - i] = domain[lookupSize - i + 1] / 2.0;
        }
        
        domain[0] = 0.0;
        domain[domain.length-1] = Double.MAX_VALUE;
                
        double[] values = new double[domain.length];
        for (int i=0; i<domain.length; i++) {
            values[i] = Math.sqrt(domain[i]);
        }

        return linearInterpolation(x, domain, values);
    }    
    
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        return array(sqrt());
    }

    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return array(lbound(MathFunctions.SQRT, constant(0.0), false));
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return array(gte(fargs[0], constant(0.0)));        
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        IfThenElse ite = lookupTable(fargs[0]);
        return array(eq(retValue, ite));
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVale) {
        return array(gte(retVale, constant(0.0)));        
    }    
}
