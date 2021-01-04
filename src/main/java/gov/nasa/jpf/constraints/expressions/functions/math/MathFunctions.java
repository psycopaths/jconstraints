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
package gov.nasa.jpf.constraints.expressions.functions.math;

public abstract class MathFunctions {

  public static UnaryDoubleFunction COS =
      new UnaryDoubleFunction("cos") {
        @Override
        protected double doEvaluate(double value) {
          return Math.cos(value);
        }
      };

  public static UnaryDoubleFunction SIN =
      new UnaryDoubleFunction("sin") {
        @Override
        protected double doEvaluate(double value) {
          return Math.sin(value);
        }
      };

  public static UnaryDoubleFunction TAN =
      new UnaryDoubleFunction("tan") {
        @Override
        protected double doEvaluate(double value) {
          return Math.tan(value);
        }
      };

  public static UnaryDoubleFunction ACOS =
      new UnaryDoubleFunction("acos") {
        @Override
        protected double doEvaluate(double value) {
          return Math.acos(value);
        }
      };

  public static UnaryDoubleFunction ASIN =
      new UnaryDoubleFunction("asin") {
        @Override
        protected double doEvaluate(double value) {
          return Math.asin(value);
        }
      };

  public static UnaryDoubleFunction ATAN =
      new UnaryDoubleFunction("atan") {
        @Override
        protected double doEvaluate(double value) {
          return Math.atan(value);
        }
      };

  public static UnaryDoubleFunction LOG =
      new UnaryDoubleFunction("log") {
        @Override
        protected double doEvaluate(double value) {
          return Math.log(value);
        }
      };

  public static UnaryDoubleFunction EXP =
      new UnaryDoubleFunction("exp") {
        @Override
        protected double doEvaluate(double value) {
          return Math.exp(value);
        }
      };

  public static UnaryDoubleFunction SQRT =
      new UnaryDoubleFunction("sqrt") {
        @Override
        protected double doEvaluate(double value) {
          return Math.sqrt(value);
        }
      };

  public static UnaryDoubleFunction LOG10 =
      new UnaryDoubleFunction("log10") {
        @Override
        protected double doEvaluate(double value) {
          return Math.log10(value);
        }
      };

  public static UnaryDoubleLongFunction ROUND =
      new UnaryDoubleLongFunction("round") {
        @Override
        protected long doEvaluate(double value) {
          return Math.round(value);
        }
      };

  public static BinaryDoubleFunction ATAN2 =
      new BinaryDoubleFunction("atan2") {
        @Override
        protected double doEvaluate(double v1, double v2) {
          return Math.atan2(v1, v2);
        }
      };

  public static BinaryDoubleFunction POW =
      new BinaryDoubleFunction("pow") {
        @Override
        protected double doEvaluate(double v1, double v2) {
          return Math.pow(v1, v2);
        }
      };

  public static UnaryIntegerFunction IABS =
      new UnaryIntegerFunction("abs") {
        @Override
        protected int doEvaluate(int v1) {
          return Math.abs(v1);
        }
      };
}
