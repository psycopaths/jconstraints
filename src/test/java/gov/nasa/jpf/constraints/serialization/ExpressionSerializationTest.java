package gov.nasa.jpf.constraints.serialization;

import static org.testng.Assert.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.StringIntegerExpression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.math.BigInteger;
import org.testng.annotations.Test;

public class ExpressionSerializationTest {

  @Test(groups = {"serialization", "base"})
  public void roundTripPropositionalCompoundTest() throws IOException, ClassNotFoundException {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");

    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(pc);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), pc.toString());
  }

  @Test(groups = {"serialization", "base"})
  public void runStringSerializationExample1Test() throws IOException, ClassNotFoundException {
    Variable str1 = Variable.create(BuiltinTypes.STRING, "_string0");
    Constant cInt0 = Constant.create(BuiltinTypes.INTEGER, BigInteger.valueOf(0));
    Expression lessThan =
        NumericBooleanExpression.create(
            cInt0, NumericComparator.LT, StringIntegerExpression.createLength(str1));
    Negation neg = Negation.create(ExpressionUtil.and(lessThan, lessThan));
    Expression finalExpr = ExpressionUtil.and(ExpressionUtil.TRUE, neg);
    finalExpr = ExpressionUtil.and(finalExpr, ExpressionUtil.TRUE);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(finalExpr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    assertEquals(read.getClass(), PropositionalCompound.class);
    assertEquals(read.toString(), finalExpr.toString());
  }

  @Test(groups = {"serialization", "base"})
  public void valuationSerializationTest() throws IOException, ClassNotFoundException {
    Valuation val = new Valuation();
    Variable str1 = new Variable(BuiltinTypes.STRING, "_string1");
    val.setValue(str1, "haha");
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(val);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Valuation readVal = (Valuation) in.readObject();
    assertEquals(readVal.getValue(str1), val.getValue(str1));
  }
}
