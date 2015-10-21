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

package gov.nasa.jpf.constraints.expressions.functions.math;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.AsinProperties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.Atan2Properties;
import gov.nasa.jpf.constraints.expressions.functions.math.axioms.SqrtProperties;
import org.testng.annotations.Test;

/**
 *
 */
@Test
public class FunctionAxiomsTest {
    
    @Test
    public void printAxiomsSin() {
        AsinProperties asin = new AsinProperties(10);
        for (Expression<Boolean> e : asin.getDefinition()) {
            System.out.println(e);
        }
    }

    @Test
    public void testLogExp() {
        System.out.println("max. " + Double.MAX_VALUE);
        double d = Math.log(Double.MAX_VALUE);
        System.out.println("log of max. " + d);
        double max = Math.exp(d);
        System.out.println("exp of log of max. " + max);

        for (int i=0; i<5; i++) {
            double x = -200.0 * (double) i;
            double e_x = Math.exp(x);
            System.out.println("exp of "+ x + ": " + e_x);
        }
    }
    
    @Test
    public void testSqrt() {
        SqrtProperties sqrt = new SqrtProperties(4);
        
        for (Expression<Boolean> e : sqrt.getDefinition()) {
            System.out.println(e);
        }
    }
    
    @Test
    public void testAtan2() {
        System.out.println("(+1.0, +1.0) " + Math.toDegrees( Math.atan2( +1.0, +1.0)) );
        System.out.println("(-1.0, +1.0) " + Math.toDegrees( Math.atan2( -1.0, +1.0)) );
        System.out.println("(-1.0, -1.0) " + Math.toDegrees( Math.atan2( -1.0, -1.0)) );
        System.out.println("(+1.0, -1.0) " + Math.toDegrees( Math.atan2( +1.0, -1.0)) );
        
        System.out.println("(+1.0, +1.0) " + Math.atan2( +1.0, +1.0) );
        System.out.println("(-1.0, +1.0) " + Math.atan2( -1.0, +1.0) );
        System.out.println("(-1.0, -1.0) " + Math.atan2( -1.0, -1.0) );
        System.out.println("(+1.0, -1.0) " + Math.atan2( +1.0, -1.0) );
      
        Atan2Properties atan2 = new Atan2Properties(11, null);
        
        for (Expression<Boolean> e : atan2.getDefinition()) {
            System.out.println(e);
        }
    }

}
