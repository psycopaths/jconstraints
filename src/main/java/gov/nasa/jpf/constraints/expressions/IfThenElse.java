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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.Type;
import java.io.IOException;
import java.util.Collection;
import java.util.Objects;

public class IfThenElse<E> extends AbstractExpression<E> {

    private final Type<E> type;
    
    private final Expression<Boolean> ifCond;
    private final Expression<E> thenExpr;    
    private final Expression<E> elseExpr;

    public IfThenElse(Type<E> type, Expression<Boolean> ifCond, Expression<E> thenExpr, Expression<E> elseExpr) {
        this.type = type;
        this.ifCond = ifCond;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }
    
    public IfThenElse(Expression<Boolean> ifCond, Expression<E> thenExpr, Expression<E> elseExpr) {
        assert thenExpr.getType().equals(elseExpr.getType());
        this.type = thenExpr.getType();
        this.ifCond = ifCond;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }
    
    @Override
    public E evaluate(Valuation values) {
        return ifCond.evaluate(values) ? thenExpr.evaluate(values) : elseExpr.evaluate(values);
    }

    @Override
    public void collectFreeVariables(Collection<? super Variable<?>> variables) {
        ifCond.collectFreeVariables(variables);
        thenExpr.collectFreeVariables(variables);
        elseExpr.collectFreeVariables(variables);
    }

    @Override
    public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
        return visitor.visit(this, data);
    }

    @Override
    public Type<E> getType() {
        return type;
    }

    @Override
    public Expression<?>[] getChildren() {
        return new Expression[] {ifCond, thenExpr, elseExpr};
    }

    @Override
    public Expression<?> duplicate(Expression<?>[] newChildren) {
        assert newChildren.length == 3;
        Expression newIf = newChildren[0];
        Expression newThen = newChildren[1];
        Expression newElse = newChildren[2];

        if(ifCond == newIf && thenExpr == newThen && elseExpr == newElse) {
          return this;
        }
        return new IfThenElse<>(this.type, ifCond, thenExpr, elseExpr);
    }

    @Override
    public void print(Appendable a, int flags) throws IOException {
        a.append("if (");
        ifCond.print(a, flags);
        a.append(") then (");
        thenExpr.print(a, flags);
        a.append(") else (");
        elseExpr.print(a, flags);
        a.append(")");
    }

    @Override
    public void printMalformedExpression(Appendable a, int flags) throws IOException{
      a.append("if (");
      if(ifCond == null){
        a.append("null");
      } else {
        ifCond.printMalformedExpression(a, flags);
      }
      a.append(") then (");
      if(thenExpr == null){
        a.append("null");
      } else{
        thenExpr.print(a, flags);
      }
      a.append(") else (");
      if(elseExpr == null){
        a.append("null");
      }else {
        elseExpr.print(a, flags);
      }
      a.append(")");
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + Objects.hashCode(this.ifCond);
        hash = 53 * hash + Objects.hashCode(this.thenExpr);
        hash = 53 * hash + Objects.hashCode(this.elseExpr);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final IfThenElse<?> other = (IfThenElse<?>) obj;
        if (!Objects.equals(this.ifCond, other.ifCond)) {
            return false;
        }
        if (!Objects.equals(this.thenExpr, other.thenExpr)) {
            return false;
        }
        if (!Objects.equals(this.elseExpr, other.elseExpr)) {
            return false;
        }
        return true;
    }

    public Expression<Boolean> getIf() {
        return ifCond;
    }

    public Expression<E> getThen() {
        return thenExpr;
    }

    public Expression<E> getElse() {
        return elseExpr;
    }
}
