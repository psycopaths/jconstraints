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
import gov.nasa.jpf.constraints.types.BuiltinTypes;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class QuantifierExpression extends AbstractBoolExpression {

  private final Quantifier quantifier;
  private final List<? extends Variable<?>> boundVariables;
  private final Expression<Boolean> body;

  public QuantifierExpression(Quantifier quantifier, List<? extends Variable<?>> boundVariables, Expression<Boolean> body) {
    this.quantifier = quantifier;
    this.boundVariables = new ArrayList<Variable<?>>(boundVariables);
    this.body = body;
  }

  public Quantifier getQuantifier() {
    return quantifier;
  }

  public List<? extends Variable<?>> getBoundVariables() {
    return Collections.unmodifiableList(boundVariables);
  }

  public Expression<Boolean> getBody() {
    return body;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final QuantifierExpression other = (QuantifierExpression) obj;

    if (this.quantifier != other.quantifier) {
      return false;
    }

    if (this.boundVariables != other.boundVariables && (this.boundVariables == null || !this.boundVariables.equals(other.boundVariables))) {
      return false;
    }

    if (this.body != other.body && (this.body == null || !this.body.equals(other.body))) {
      return false;
    }

    return true;
  }

  @Override
  public int hashCode() {
    int hash = 3;
    hash = 43 * hash + quantifier.hashCode();
    hash = 43 * hash + boundVariables.hashCode();
    hash = 43 * hash + body.hashCode();
    return hash;
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append('(').append(quantifier.toString()).append(" (");
    boolean first = true;
    int varDeclFlags = flags;
    if (includeBoundDeclType(flags)) {
      varDeclFlags |= INCLUDE_VARIABLE_TYPE;
    }

    for (Variable<?> var : boundVariables) {
      if (first) {
        first = false;
      } else {
        a.append(", ");
      }
      var.print(a, varDeclFlags);
    }
    a.append("): ");
    body.print(a, flags);
    a.append(')');
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) 
          throws IOException{
    a.append('(').append(quantifier.toString()).append(" (");
    boolean first = true;
    int varDeclFlags = flags;
    if (includeBoundDeclType(flags)) {
      varDeclFlags |= INCLUDE_VARIABLE_TYPE;
    }

    for (Variable<?> var : boundVariables) {
      if (first) {
        first = false;
      } else {
        a.append(", ");
      }
      if(var != null){
        var.print(a, varDeclFlags);
      }else{
        a.append("null");
      }
    }
    a.append("): ");
    if(body != null){
      body.print(a, flags);
    }else{
      a.append("null");
    }
    a.append(')');
  }

  @Override
  public Boolean evaluate(Valuation values) {
    throw new UnsupportedOperationException("Evaluation not supported for quantifiers");
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    // Omit bound variables 
    // List of bound variables that DO NOT appear in the outer scope
    List<Variable<?>> boundOnly = new ArrayList<Variable<?>>();
    for (Variable<?> v : boundVariables) {
      if (!variables.contains(v)) {
        boundOnly.add(v);
      }
    }
    body.collectFreeVariables(variables);
    variables.removeAll(boundOnly);
  }

  @Override
  public Expression<?>[] getChildren() {
    return new Expression[]{body};
  }

  @Override
  public Expression<Boolean> duplicate(
          Expression<?>[] newChildren) {
    assert newChildren.length == 1;

    Expression<?> newBody = newChildren[0];
    if (body == newBody) {
      return this;
    }
    return new QuantifierExpression(this.quantifier, boundVariables, newBody.as(BuiltinTypes.BOOL));
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    return visitor.visit(this, data);
  }

}
