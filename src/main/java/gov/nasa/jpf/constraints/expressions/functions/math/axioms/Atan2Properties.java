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
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.IfThenElse;
import gov.nasa.jpf.constraints.expressions.QuantifierExpression;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.BinaryDoubleFunction;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;
import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import static gov.nasa.jpf.constraints.util.ExpressionUtil.and;

public class Atan2Properties implements FunctionProperties {

    public static final Function ATAN2_LOOKUP = new BinaryDoubleFunction("atan2_lookup") {
        @Override
        protected double doEvaluate(double v1, double v2) {
            throw new UnsupportedOperationException("Not supported yet."); 
        }
    };

    public static final Function ATAN2_Y_POS = new BinaryDoubleFunction("atan2_y_pos") {
        @Override
        protected double doEvaluate(double v1, double v2) {
            throw new UnsupportedOperationException("Not supported yet."); 
        }
    };    
    
    private final int lookupSize;
    
    private final SqrtProperties sqrt;

    public Atan2Properties(int lookupSize, SqrtProperties sqrt) {
        this.lookupSize = lookupSize;
        this.sqrt = sqrt;
    }
    
    
    private Expression<Boolean> bounds(Expression x, double lower, double upper, 
            boolean openLower, boolean openUpper, Expression scale) {
        Constant cl = new Constant(BuiltinTypes.DOUBLE, lower);
        Constant cu = new Constant(BuiltinTypes.DOUBLE, upper);

        Expression<Boolean> lBound = openLower ? lt(mul(cl, scale), x) : lte(mul(cl, scale), x);
        Expression<Boolean> uBound = openUpper ? lt(x, mul(cu, scale)) : lte(x, mul(cu, scale));
        return and(lBound, uBound);
    }
    
    private IfThenElse linearInterpolation(Expression x, Expression scale, 
            double[] dVals, double[] fVals) {

        assert dVals.length == fVals.length;
        assert dVals.length > 2;
        
        Expression[] itp = new Expression[dVals.length - 1];
        for (int i = 0; i < itp.length; i++) {
            itp[i] = interpolate(x, fVals[i], fVals[i + 1], dVals[i], dVals[i + 1]);
        }

        IfThenElse ite = ite(bounds(x, dVals[dVals.length - 3], dVals[dVals.length - 2], false, false, scale),
                itp[itp.length - 2], itp[itp.length - 1]);

        for (int i = 3; i < dVals.length; i++) {
            ite = ite(bounds(x, dVals[dVals.length - i - 1], dVals[dVals.length - i], false, false, scale),
                    itp[itp.length - i], ite);
        }

        return ite;
    }        

    private Expression<Boolean> lookupTable() {
        Variable y = var(BuiltinTypes.DOUBLE);
        Variable x = var(BuiltinTypes.DOUBLE);
        
        Expression scale = fexpr(MathFunctions.SQRT, plus(mul(x,x), mul(y,y)));
        FunctionExpression fe = fexpr(ATAN2_LOOKUP, y, x);
        
        IfThenElse ite = lookupTable(x, scale);
        
        Expression<Boolean> equal = eq(fe, ite);
        QuantifierExpression qf = forall(equal, x, y);
        
        return qf;
    }
         
    private IfThenElse lookupTable(Expression x, Expression scale) {
        double[] domain = interval(0 , 90.0, lookupSize);
        double[] values = new double[domain.length];
        for (int i=0; i<domain.length; i++) {
            double t = Math.toRadians(domain[i]);
            double _x = Math.cos(t);
            double _y = Math.sin(t);
            domain[i] = _x;
            values[i] = Math.atan2(_y, _x);
            // assert values[i] == t;
        }

        return linearInterpolation(x, scale, domain, values);
    }    
    
    private Expression<Boolean> atan2_y_pos() {
        Variable x = doubleVar();                
        Variable y = doubleVar();                
        Expression<Boolean> ifCond = gte(x, constant(0.0));
        Expression thenExpr = fexpr(ATAN2_LOOKUP, y, x);
        Expression elseExpr = minus(constant(180.0), fexpr(ATAN2_LOOKUP, y, new UnaryMinus(x)));        
        return forall(eq(fexpr(ATAN2_Y_POS, y, x), 
                ite(ifCond, thenExpr, elseExpr)), x, y);                        
    }
    
    private Expression<Boolean> atan2_y_pos(Expression x, Variable ret,
            Variable xLookup,  Variable retLookup) {
    
        Expression<Boolean> ifCond = gte(x, constant(0.0));
        Expression thenExprArgX = x;
        Expression thenExprRet = retLookup;
        
        Expression elseExprArgX = new UnaryMinus<>(x);
        Expression elseExprRet = minus(constant(180.0), retLookup);
        
        return ExpressionUtil.and(
                eq(xLookup, ite(ifCond, thenExprArgX, elseExprArgX)),
                eq(ret, ite(ifCond, thenExprRet, elseExprRet))
        );
    }
    
    private Expression<Boolean> atan2() {
        Variable x = doubleVar();                
        Variable y = doubleVar();                
        
        // y>=0 => atan2_y_pos(y,x)
        // y<0 => -atan2(-y,x)
        Expression<Boolean> ifCond = gte(y, constant(0.0));
        Expression thenExpr = fexpr(ATAN2_Y_POS, y, x);
        Expression elseExpr = new UnaryMinus(fexpr(ATAN2_Y_POS, new UnaryMinus(y), x));
        
        // y=0, x=0 
        elseExpr = ite(ifCond, thenExpr, elseExpr);
        thenExpr = constant(Math.atan2(0.0, 0.0));
        ifCond = ExpressionUtil.and( eq(x, constant(0.0)), eq(y, constant(0.0)));

        return forall(eq(fexpr(MathFunctions.ATAN2, y, x), 
                ite(ifCond, thenExpr, elseExpr)), x, y);  
    }
    
    private Expression<Boolean> atan2(Expression x, Expression y, Variable ret, Variable ret_y_pos) {
                
        Expression<Boolean> ifCond = gte(y, constant(0.0));
        
        Expression thenExprRet  = ret_y_pos;
        Expression elseExprRet  = new UnaryMinus(ret_y_pos);

        elseExprRet  = ite(ifCond, thenExprRet, elseExprRet);
        
        // y=0, x=0 
        ifCond = ExpressionUtil.and( eq(x, constant(0.0)), eq(y, constant(0.0)));        
        thenExprRet = constant(Math.atan2(0.0, 0.0));

        return ExpressionUtil.and(
                eq(ret, ite(ifCond, thenExprRet, elseExprRet))
        );
    }
    
    @Override
    public Expression<Boolean>[] getDefinition() {
        return array(lookupTable(), atan2_y_pos(), atan2());
    }

    @Override
    public Expression<Boolean>[] getRangeBounds() {
        return array(PropertyBuilder.bounds(MathFunctions.ATAN2, constant(-Math.PI), constant(Math.PI), false));    
    }

    @Override
    public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
        return array();    
    }
    
    @Override
    public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
        
        Expression y = fargs[0];
        Expression x = fargs[1];
        
        Variable scale = var(BuiltinTypes.DOUBLE);
        Expression scaleArg = plus(mul(x,x), mul(y,y));
        
        Variable x_lookup = var(BuiltinTypes.DOUBLE);
        Variable atan2_lookup = var(BuiltinTypes.DOUBLE);
        
        Variable atan2_y_pos = var(BuiltinTypes.DOUBLE);
        
        return array(
                sqrt.getDefinition(scale, scaleArg)[0],
                eq(atan2_lookup, lookupTable(x_lookup, scale)),
                atan2_y_pos(x, atan2_y_pos, x_lookup, atan2_lookup),
                atan2(x, y, retValue, atan2_y_pos)
        );        
    }
    
    @Override
    public Expression<Boolean>[] getRangeBounds(Variable retVal) {
        return array(PropertyBuilder.bounds(retVal, -Math.PI, Math.PI, false, false));    
    }    
    
}
