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
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

import java.util.Properties;
import org.testng.annotations.Test;

public class ModuloTestZ3 {

  @Test
  public void moduloTest() {

    
    Properties conf = new Properties();    
    conf.setProperty("symbolic.dp","NativeZ3");

    // construct expression
    
    Variable<Integer> var_i1 = Variable.create(BuiltinTypes.SINT32, "i1");    
    
    Constant<Integer> const_2 = Constant.create(BuiltinTypes.SINT32, 2);
    Constant<Integer> const_1 = Constant.create(BuiltinTypes.SINT32, 1);

    
    NumericCompound<Integer> inner = NumericCompound.create(
            var_i1, NumericOperator.REM, const_2);
        
    NumericBooleanExpression expr = NumericBooleanExpression.create(
            inner, NumericComparator.EQ, const_1);
            
    System.out.println(expr);
    
    // solve

//    m.setIntMin(0);
//    m.setVarMax(var_i1, 0.100);
    
    ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
    ConstraintSolver solver = factory.createSolver();
        
    Valuation val = new Valuation();    
    ConstraintSolver.Result result = solver.solve(expr, val);
    System.out.println(result);
    System.out.println(val);    
    
    
    Variable<Float> var_f1 = Variable.create(BuiltinTypes.FLOAT, "f1");
    
    Constant<Float> consta = Constant.create(BuiltinTypes.FLOAT, 5.4f);
    Constant<Float> constb = Constant.create(BuiltinTypes.FLOAT, -2.6f);
    
    NumericBooleanExpression expr2 = NumericBooleanExpression.create(
        var_f1, NumericComparator.EQ, NumericCompound.create(consta, NumericOperator.REM, constb));
    
    Valuation val2 = new Valuation();
    
    System.out.println(expr2);
    result = solver.solve(expr2, val2);
    
    System.out.println("Valuation " + val2);
    System.out.println("Java says " + (consta.getValue() % constb.getValue()));
    
    Constant<Float> constc = Constant.create(BuiltinTypes.FLOAT, -21.2f);
    Constant<Float> constd = Constant.create(BuiltinTypes.FLOAT, 7.02f);
    
    NumericBooleanExpression expr3 = NumericBooleanExpression.create(
        var_f1, NumericComparator.EQ, NumericCompound.create(constc, NumericOperator.REM, constd));
    
    Valuation val3 = new Valuation();
    
    System.out.println(expr3);
    result = solver.solve(expr3, val3);
    
    System.out.println("Valuation " + val3);
    System.out.println("Java says " + (constc.getValue() % constd.getValue()));
    
//    System.out.println("" + (-1 % 2));    
  }
  
  
}
