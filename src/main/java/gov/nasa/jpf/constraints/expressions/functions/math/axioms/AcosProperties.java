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
package gov.nasa.jpf.constraints.expressions.functions.math.axioms;

import static gov.nasa.jpf.constraints.expressions.functions.math.axioms.PropertyBuilder.*;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.functions.math.MathFunctions;

public class AcosProperties implements FunctionProperties {

  @Override
  public Expression<Boolean>[] getDefinition() {
    Variable arg = doubleVar();

    Expression eval = minus(constant(Math.PI * 0.5), fexpr(MathFunctions.ASIN, arg));
    Expression<Boolean> acos = forall(eq(fexpr(MathFunctions.ACOS, arg), eval), arg);
    return array(acos);
  }

  @Override
  public Expression<Boolean>[] getRangeBounds() {
    // FIXME: the computed value for 1.0 is not within these bounds!!!
    return array(bounds(MathFunctions.ACOS, constant(0.0), constant(Math.PI), false));
  }

  @Override
  public Expression<Boolean>[] getDomainBounds(Expression... fargs) {
    return array(bounds(fargs[0], -1.0, 1.0, false, false));
  }

  @Override
  public Expression<Boolean>[] getDefinition(Variable retValue, Expression... fargs) {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public Expression<Boolean>[] getRangeBounds(Variable retVal) {
    return array(bounds(retVal, 0.0, Math.PI, false, false));
  }
}
