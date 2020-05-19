/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import static org.testng.Assert.assertTrue;
import org.testng.annotations.BeforeSuite;
import org.testng.annotations.BeforeTest;
import org.testng.annotations.Test;

@Test
public class PrintTest {
  
  Expression exprUnderTest;
  @BeforeTest(alwaysRun = true)
  public void setupExpression(){
    Variable var1 = Variable.create(BuiltinTypes.SINT32, "X");
    Variable var2 = Variable.create(BuiltinTypes.SINT32, "Y");
    Constant c1 = Constant.create(BuiltinTypes.SINT32, 5);
    Constant c2 = Constant.create(BuiltinTypes.SINT32, 8);
    
    NumericCompound compound1 = 
            new NumericCompound(var1, NumericOperator.PLUS, c1);
    NumericCompound compound2 = 
            new NumericCompound(var1, NumericOperator.MINUS, c2);
    NumericBooleanExpression bool1 = 
            new NumericBooleanExpression(var2, NumericComparator.EQ, null);
    NumericBooleanExpression bool2 = 
            new NumericBooleanExpression(null, NumericComparator.EQ, c2);
    PropositionalCompound compound3 = 
            new PropositionalCompound(bool1, LogicalOperator.OR, bool2);
    exprUnderTest = compound3;
  }

  @Test(groups = {"expressions", "base"})
  public void testMalformedPrint() {
    StringBuilder builder = new StringBuilder();
    try {
      exprUnderTest.printMalformedExpression(builder);
    } catch (IOException ex) {
    }
    String result = builder.toString();
    assertTrue(result.contains("null"));
  }

  @Test(expectedExceptions = {NullPointerException.class}, groups = {"expressions", "base"})
  public void testPrint(){
    StringBuilder builder = new StringBuilder();
    try{
    exprUnderTest.print(builder);
    }catch(IOException e){
    }
  }
}
