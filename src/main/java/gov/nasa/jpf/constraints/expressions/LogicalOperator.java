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

/**
 * operator for logic formulas
 */
public enum LogicalOperator {

  AND("&&") { public boolean eval(boolean lv, boolean rv) { return lv && rv; } }, 
  OR("||") { public boolean eval(boolean lv, boolean rv) { return lv || rv; } }, 
  IMPLY("->") { public boolean eval(boolean lv, boolean rv) { return !lv || rv; } }, 
  EQUIV("<->") { public boolean eval(boolean lv, boolean rv) { return lv == rv; } }, 
  XOR("^") { public boolean eval(boolean lv, boolean rv) { return lv ^ rv; } };

  private final String str;
  
  private LogicalOperator(final String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static LogicalOperator fromString(String str){
    switch(str){
      case "&&": return AND;
      case "||": return OR;
      case "->": return IMPLY;
      case "<->": return EQUIV;
      case "^": return XOR;
      default: return null;
    }
  }

  public abstract boolean eval(boolean lv, boolean rv);
}
