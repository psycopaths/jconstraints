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
package gov.nasa.jpf.constraints.solvers.nativez3;

import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import static com.microsoft.z3.enumerations.Z3_sort_kind.Z3_BOOL_SORT;
import static com.microsoft.z3.enumerations.Z3_sort_kind.Z3_BV_SORT;
import static com.microsoft.z3.enumerations.Z3_sort_kind.Z3_INT_SORT;
import static com.microsoft.z3.enumerations.Z3_sort_kind.Z3_REAL_SORT;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.BitvectorExpression;
import gov.nasa.jpf.constraints.expressions.BitvectorOperator;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.LogicalOperator;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Pattern;

public class NativeZ3TojConstraintConverter {

  private Logger logger;

  public NativeZ3TojConstraintConverter() {
    logger = Logger.getLogger("z3");
  }

  public Expression<Boolean> parse(Expr z3Expr) {
    logger.info("parse:" + z3Expr);
    Expression<Boolean> returnExpression = null;
    ArrayList<Expression<Boolean>> arguments = convertArgs(z3Expr.getArgs());
    if (z3Expr.isAnd()) {
      returnExpression = ExpressionUtil.and(arguments);
    }
    if (z3Expr.isOr()) {
      returnExpression = ExpressionUtil.or(arguments);
    }
    if (z3Expr.isXor()) {
      returnExpression
              = ExpressionUtil.combine(LogicalOperator.XOR, null, arguments);
    }
    if (z3Expr instanceof BoolExpr) {
      if (z3Expr.isTrue()) {
        returnExpression = Constant.create(BuiltinTypes.BOOL, true);
      } else if (z3Expr.isFalse()) {
        returnExpression = Constant.create(BuiltinTypes.BOOL, false);
      } else {
        //This is actually happening in z3Expr... Fix me
        returnExpression
                = new Variable(BuiltinTypes.BOOL, z3Expr.toString());
      }
    }
    if (z3Expr instanceof IntNum) {
      String value = ((IntNum) z3Expr).toString();
      returnExpression = new Constant(BuiltinTypes.INTEGER,
              value);
    }
    if (z3Expr instanceof IntExpr) {
      String name = ((IntExpr) z3Expr).toString();
      returnExpression = new Variable(BuiltinTypes.INTEGER, name);

    }
    if (z3Expr instanceof BitVecExpr) {
      try {
        returnExpression = parseBitVector(z3Expr, arguments);
      } catch (Exception ex) {
        logger.log(Level.SEVERE, null, ex);
      }
    }
    if (arguments.size() == 1) {
      if (z3Expr.isUMinus()) {
        returnExpression = UnaryMinus.create(arguments.get(0));
      }
      if (z3Expr.isNot()) {
        returnExpression = new Negation(arguments.get(0));
      }
    }
    if (arguments.size() == 2) {
      if (z3Expr.isAdd()) {
        returnExpression
                = NumericCompound.create(arguments.get(0),
                        NumericOperator.PLUS, arguments.get(1));
      }
      if (z3Expr.isMul()) {
        returnExpression
                = NumericCompound.create(arguments.get(0),
                        NumericOperator.MUL, arguments.get(1));
      }
      if (z3Expr.isDiv()) {
        returnExpression
                = NumericCompound.create(arguments.get(0),
                        NumericOperator.DIV, arguments.get(1));
      }
      if (z3Expr.isRemainder()) {
        returnExpression
                = NumericCompound.create(arguments.get(0),
                        NumericOperator.REM, arguments.get(1));
      }
      if (z3Expr.isSub()) {
        returnExpression
                = NumericCompound.create(arguments.get(0),
                        NumericOperator.MINUS, arguments.get(1));
      }
      if (z3Expr.isGT()) {
        returnExpression
                = NumericBooleanExpression.create(arguments.get(0),
                        NumericComparator.GT, arguments.get(1));
      }
      if (z3Expr.isGE()) {
        returnExpression
                = NumericBooleanExpression.create(arguments.get(0),
                        NumericComparator.GE, arguments.get(1));
      }
      if (z3Expr.isLT()) {
        returnExpression
                = NumericBooleanExpression.create(arguments.get(0),
                        NumericComparator.LT, arguments.get(1));
      }
      if (z3Expr.isLE()) {
        returnExpression
                = NumericBooleanExpression.create(arguments.get(0),
                        NumericComparator.LE, arguments.get(1));
      }
      if (z3Expr.isEq()) {
        returnExpression
                = NumericBooleanExpression.create(arguments.get(0),
                        NumericComparator.EQ, arguments.get(1));
      }
      if (z3Expr.isModulus()) {
        throw new UnsupportedOperationException(
                "jConstraint does not support Modulus yet.");
      }
    }
    if (returnExpression == null) {
      String msg = "Cannot convert the z3Expression to jConstraint";
      logger.severe(msg);
      throw new UnsupportedOperationException(msg);
    }
    return returnExpression;
  }

  private ArrayList<Expression<Boolean>> convertArgs(Expr[] args) {
    ArrayList<Expression<Boolean>> converted = new ArrayList<>();
    for (Expr expr : args) {
      converted.add(parse(expr));
    }
    return converted;
  }

  private Expression<Boolean> parseBitVector(Expr z3Expr, ArrayList<Expression<Boolean>> arguments) throws Exception {
    if (z3Expr.isBVAND()) {
      return new BitvectorExpression<>(arguments.get(0),
              BitvectorOperator.AND, arguments.get(1));
    }
    if (z3Expr.isBVSLT()) {
      return new NumericBooleanExpression(arguments.get(0),
              NumericComparator.LT, arguments.get(1));
    }
    if (z3Expr instanceof BitVecExpr) {
      if (z3Expr.isInt()) {
        return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
      }
      switch (z3Expr.getSort().getSortKind()) {
        case Z3_BOOL_SORT:
          return new Variable(BuiltinTypes.BOOL, z3Expr.toString());
        case Z3_INT_SORT:
          return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
        case Z3_REAL_SORT:
          return new Variable(BuiltinTypes.DECIMAL, z3Expr.toString());
        case Z3_BV_SORT:
          return new Variable(BuiltinTypes.INTEGER, z3Expr.toString());
        default:
          throw new Exception("Unknown Sort");
      }
    }
    return null;
  }

}
