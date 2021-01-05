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
package gov.nasa.jpf.constraints.expressions;

public enum RegExOperator implements ExpressionOperator {
  KLEENESTAR("re.*"),
  KLEENEPLUS("re.+"),
  LOOP("re.loop"),
  RANGE("re.range"),
  OPTIONAL("re.opt"),
  STRTORE("str.to.re"),
  ALLCHAR("re.allchar"),
  ALL("re.all"),
  COMPLEMENT("re.comp"),
  NOSTR("re.nostr");

  private final String str;

  RegExOperator(String str) {
    this.str = str;
  }

  @Override
  public String toString() {
    return str;
  }

  public static RegExOperator fromString(String str) {
    switch (str) {
      case "re.loop":
        return LOOP;
      case "re.range":
        return RANGE;
      case "re.*":
        return KLEENESTAR;
      case "re.+":
        return KLEENEPLUS;
      case "re.opt":
        return OPTIONAL;
      case "str.to.re":
        return STRTORE;
      case "re.allchar":
        return ALLCHAR;
      case "re.all":
        return ALL;
      case "re.nostr":
        return NOSTR;
      case "re.comp":
        return COMPLEMENT;
      default:
        return null;
    }
  }
}
