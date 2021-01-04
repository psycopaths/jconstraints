/**
 * Copyright 2020, TU Dortmund, Malte Mues (@mmuesly)
 *
 * This is a derived version of JConstraints original located at:
 * https://github.com/psycopaths/jconstraints
 *
 * Until commit: https://github.com/tudo-aqua/jconstraints/commit/876e377
 * the original license is:
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
 *
 * Modifications and new contributions are Copyright by TU Dortmund 2020, Malte Mues
 * under Apache 2.0 in alignment with the original repository license.
 */
package gov.nasa.jpf.constraints.simplifiers.datastructures;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class AssignmentCollector {

  private Map<Variable, List<Expression>> assignments;
  private Map<Variable, List<Expression>> eventuallyPrune;
  private int insideNegation = 0;

  public AssignmentCollector() {
    assignments = new HashMap<>();
    eventuallyPrune = new HashMap<>();
  }

  public void addAssignment(Variable v, Expression e, Expression originalAssignment) {
    List assignmentForVar = assignments.getOrDefault(v, new ArrayList<>());
    assignmentForVar.add(e);
    assignments.put(v, assignmentForVar);

    List prune = eventuallyPrune.getOrDefault(v, new ArrayList<>());
    prune.add(originalAssignment);
    eventuallyPrune.put(v, prune);
  }

  public ArithmeticVarReplacements convertToArithmeticVarReplacements() {
    Map<Variable, Expression> replacements = new HashMap<>();
    for (Variable v : assignments.keySet()) {
      List<Expression> assignementsForVar = assignments.getOrDefault(v, new ArrayList<>());
      if (assignementsForVar.size() == 1) {
        Expression replacement = assignementsForVar.get(0);
        if (!(replacement instanceof NumericBooleanExpression)) {
          replacements.put(v, replacement);
          if (eventuallyPrune.get(v).size() != 1) {
            throw new AssignmentCollectionException("Expected exactly one expressions in pruning.");
          }
          continue;
        }
      }
      eventuallyPrune.remove(v);
    }
    boolean changed;
    ArithmeticVarReplacements ret = new ArithmeticVarReplacements(replacements);
    do {
      changed = false;
      for (Variable v : replacements.keySet()) {
        Expression replacement = replacements.get(v);
        if (replacement instanceof Variable && replacements.keySet().contains(replacement)) {
          replacements.put(v, replacements.get(replacement));
          changed = true;
        }
        Expression transformedReplacement = ExpressionUtil.transformVars(replacement, ret);
        if (!replacement.equals(transformedReplacement)) {
          replacements.put(v, transformedReplacement);
          changed = true;
        }
      }
      ret = new ArithmeticVarReplacements(replacements);
    } while (changed);
    return ret;
  }

  public List<Expression> getToPrune() {
    List<Expression> toBePruned = new ArrayList<Expression>();
    for (List<Expression> v : eventuallyPrune.values()) {
      toBePruned.addAll(v);
    }
    return toBePruned;
  }

  public void enterNegation() {
    ++this.insideNegation;
  }

  public void exitNegation() {
    --this.insideNegation;
  }

  public boolean isNegation() {
    return this.insideNegation > 0;
  }
}
