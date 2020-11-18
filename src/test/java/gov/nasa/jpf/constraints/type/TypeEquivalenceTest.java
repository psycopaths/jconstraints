package gov.nasa.jpf.constraints.type;

import static org.testng.Assert.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.BuiltinTypes.BoolType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import org.testng.annotations.Test;

public class TypeEquivalenceTest {

  @Test(groups = {"basic", "types"})
  public void booleanTypeTest() throws IOException, ClassNotFoundException {
    Constant<Boolean> c0 = Constant.create(new BoolType(), true);
    Type t = c0.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant c1 = (Constant) serializeAndDeserialize(c0);
    t = c1.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant c2 = (Constant) serializeAndDeserialize(ExpressionUtil.TRUE);
    t = c2.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    Constant c3 = (Constant) serializeAndDeserialize(ExpressionUtil.FALSE);
    t = c3.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }

  private Expression serializeAndDeserialize(Expression expr)
      throws IOException, ClassNotFoundException {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ObjectOutputStream objectOut = new ObjectOutputStream(out);
    objectOut.writeObject(expr);
    ObjectInputStream in = new ObjectInputStream(new ByteArrayInputStream(out.toByteArray()));
    Object read = in.readObject();
    return (Expression) read;
  }

  @Test(groups = {"basic", "types"})
  public void booleanType2Test() throws IOException, ClassNotFoundException {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");
    Variable b = Variable.create(BuiltinTypes.BOOL, "b");
    PropositionalCompound pc = PropositionalCompound.create(a, LogicalOperator.EQUIV, b);

    PropositionalCompound pc1 = (PropositionalCompound) serializeAndDeserialize(pc);
    Type t = pc1.getLeft().getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);

    t = pc1.getRight().getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }

  @Test(groups = {"basic", "types"})
  public void booleanVarType2Test() throws IOException, ClassNotFoundException {
    Variable a = Variable.create(BuiltinTypes.BOOL, "a");

    Variable a1 = (Variable) serializeAndDeserialize(a);
    Type t = a1.getType();
    assertTrue(t.equals(BuiltinTypes.BOOL));
    assertTrue(t instanceof BuiltinTypes.BoolType);
  }
}
