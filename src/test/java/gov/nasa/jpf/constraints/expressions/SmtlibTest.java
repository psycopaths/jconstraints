/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * Redistribution with Modifications of jconstraints-z3:
 * https://github.com/tudo-aqua/jconstraints-z3/commit/a9ab06a29f426cc3f1dd1f8406ebba8b65cf9f5d
 *
 * <p>Copyright (C) 2015, United States Government, as represented by the Administrator of the
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
 * <p>Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
 * except in compliance with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * <p>Unless required by applicable law or agreed to in writing, software distributed under the
 * License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * <p>Modifications are Copyright 2020 TU Dortmund, Malte Mues (@mmuesly, mail.mues@gmail.com) We
 * license the changes and additions to this repository under Apache License, Version 2.0.
 */
package gov.nasa.jpf.constraints.expressions;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParser;
import gov.nasa.jpf.constraints.smtlibUtility.parser.SMTLIBParserException;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import java.io.IOException;
import java.util.Properties;

public class SmtlibTest {
  public static void main(String args[])
      throws IOException, SMTLIBParserException {
    SMTProblem problem =
        SMTLIBParser.parseSMTProgram(
            "(declare-fun I0_2 () Int)\n"
                + "(declare-fun I1_2 () Int)\n"
                + "(declare-fun I2_2 () Int)\n"
                + "(declare-fun PCTEMP_LHS_1 () String)\n"
                + "(declare-fun T1_2 () String)\n"
                + "(declare-fun T2_2 () String)\n"
                + "(declare-fun T3_2 () String)\n"
                + "(declare-fun T_2 () Bool)\n"
                + "(declare-fun var_0xINPUT_2 () String)\n"
                + "(assert (= I0_2 (- 5 0)))\n"
                + "(assert (>= 0 0))\n"
                + "(assert (>= 5 0))\n"
                + "(assert (<= 5 I1_2))\n"
                + "(assert (= I2_2 I1_2))\n"
                + "(assert (= I0_2 (str.len PCTEMP_LHS_1)))\n"
                + "(assert (= var_0xINPUT_2 (str.++ T1_2 T2_2)))\n"
                + "(assert (= T2_2 (str.++ PCTEMP_LHS_1 T3_2)))\n"
                + "(assert (= 0 (str.len T1_2)))\n"
                + "(assert (= I1_2 (str.len var_0xINPUT_2)))\n"
                + "(assert (= T_2 (not (= PCTEMP_LHS_1 \"hello\"))))\n"
                + "(assert T_2)\n"
                + "(check-sat)");
    Properties conf = new Properties();
    conf.setProperty("symbolic.dp", "z3");
    conf.setProperty("z3.options", "smt.string_solver=seq");
    ConstraintSolverFactory factory = new ConstraintSolverFactory();
    ConstraintSolver solver = factory.createSolver("z3");
    Valuation val = new Valuation();
    Result result = solver.solve(problem.getAllAssertionsAsConjunction(), val);
    System.out.println("Result: " + result);
    System.out.println("Valuation: " + val);
  }
}
