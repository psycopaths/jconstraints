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

package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.Type;

final class StripPrefixVisitor extends DuplicatingVisitor<String> {
  
  public static final StripPrefixVisitor INSTANCE = new StripPrefixVisitor();

  /* (non-Javadoc)
   * @see gov.nasa.jpf.constraints.api.AbstractExpressionVisitor#visit(gov.nasa.jpf.constraints.api.Variable, java.lang.Object)
   */
  @Override
  public <E> Expression<E> visit(Variable<E> v,
      String prefix) {
    String name = v.getName();
    if(!name.startsWith(prefix))
      return v;
    return Variable.create(v.getType(), name.substring(prefix.length()));
  }
  
  public <E> Expression<E> apply(Expression<E> expr, String prefix) {
    Type<E> type = expr.getType();
    return visit(expr, prefix).as(type);
  }
}
