/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.solver;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.solvers.nativez3.NativeZ3TojConstraintConverter;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.junit.Before;
import org.testng.annotations.Test;

/**
 *
 * @author mmuesly
 */
public class ExpressionConversionTest {
  
  public ExpressionConversionTest() {
  }
  
  @Before
  public void setUp() {
  }

  @Test
  public void testExpressionConversion(){
    String z3ExprString = "(exists ('a':integer, 'b':integer):"
            +" ((('x' == ('a' + 'b')) && ('a' > 0)) && ('b' > 0)))";
    //System.out.println("gov.nasa.jpf.constraints.solver.ExpressionConversionTest.testExpressionConversion() - convCreation");
    NativeZ3TojConstraintConverter converter = new NativeZ3TojConstraintConverter();
    //Expression<Boolean> test = converter.parse("(>= x 2)");
    //System.out.println("gov.nasa.jpf.constraints.solver.ExpressionConversionTest.testExpressionConversion() - expressionResult");
//    try {
//      test.print(System.out);
//    } catch (IOException ex) {
//      Logger.getLogger(ExpressionConversionTest.class.getName()).log(Level.SEVERE, null, ex);
//    }
  }
}
