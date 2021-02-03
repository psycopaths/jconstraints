/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * <p>This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * <p>Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377 the original license
 * is: Copyright (C) 2015, United States Government, as represented by the Administrator of the
 * National Aeronautics and Space Administration. All rights reserved.
 *
 * <p>The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment platform is licensed
 * under the Apache License, Version 2.0 (the "License"); you may not use this file except in
 * compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0.
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues under Apache
 * 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.ExpressionVisitor;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.simplifiers.datastructures.ArithmeticVarReplacements;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/*
 * Author: Malte Mues (@mmuesly mail.mues@gmail.com)
 */
public class LetExpression extends EqualityExpression {
  private final List<Variable> variables;
  private final Map<Variable, Expression> values;
  private final Expression mainValue;

  public LetExpression(
      List<Variable> variables, Map<Variable, Expression> values, Expression main) {
    super();
    this.variables = variables;
    this.values = values;
    this.mainValue = main;
  }

  public LetExpression(Variable var, Expression value, Expression mainValue) {
    super();
    this.variables = new ArrayList<>();
    this.variables.add(var);
    this.values = new HashMap<>();
    this.values.put(var, value);
    this.mainValue = mainValue;
  }

  public static LetExpression create(Variable var, Expression value, Expression mainValue) {
    return new LetExpression(var, value, mainValue);
  }

  public static LetExpression create(
      List<Variable> variables, Map<Variable, Expression> values, Expression main) {
    return new LetExpression(variables, values, main);
  }

  @Override
  public Boolean evaluate(Valuation values) {
    Expression<Boolean> flattened = this.flattenLetExpression();
    return flattened.evaluate(values);
  }

  @Override
  public Boolean evaluateSMT(Valuation values) {
    Expression<Boolean> flattened = this.flattenLetExpression();
    return flattened.evaluateSMT(values);
  }

  @Override
  public void collectFreeVariables(Collection<? super Variable<?>> variables) {
    Expression<Boolean> flattened = this.flattenLetExpression();
    flattened.collectFreeVariables(variables);
  }

  @Override
  public <R, D> R accept(ExpressionVisitor<R, D> visitor, D data) {
    /* TODO: This is not a universal valid implementation, I guess.
     *
     * One Idea to fix this, is replacing of Let expressions into a single expression and then apply
     * the visitor without any further problems on the Let-Expression free form. Any other opinions
     */
    return visitor.visit(this, data);
  }

  @Override
  public Expression<?>[] getChildren() {
    throw new UnsupportedOperationException(
        "It is not totally cleare, what is a child in a LetExpression.");
  }

  @Override
  public Expression<?> duplicate(Expression<?>[] newChildren) {
    HashMap<Variable, Expression> copiedValues = new HashMap<>();
    for (Variable var : values.keySet()) {
      copiedValues.put(var, values.getOrDefault(var, var).duplicate(newChildren));
    }
    Expression copiedMain = mainValue.duplicate(newChildren);
    return new LetExpression(variables, copiedValues, copiedMain);
  }

  @Override
  public void print(Appendable a, int flags) throws IOException {
    a.append("With (");
    for (Variable var : variables) {
      a.append("( " + var.getName() + " == ");
      values.getOrDefault(var, var).print(a, flags);
      a.append(") solve ( ");
    }
    mainValue.print(a, flags);
    a.append(")");
  }

  @Override
  public void printMalformedExpression(Appendable a, int flags) throws IOException {
    throw new UnsupportedOperationException("This call is not yet supported.");
  }

  public List<Variable> getParameters() {
    return variables;
  }

  public Map<Variable, Expression> getParameterValues() {
    return values;
  }

  public Expression getMainValue() {
    return mainValue;
  }

  public Expression flattenLetExpression() {
    return ExpressionUtil.transformVars(mainValue, new ArithmeticVarReplacements(values));
  }
}
