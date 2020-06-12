/**
 * Copyright 2020 TU Dortmund, Nils Schmidt und Malte Mues
 * <p>
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * <p>
 * http://www.apache.org/licenses/LICENSE-2.0
 * <p>
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */
package io.github.tudoaqua.jconstraints.cvc4;

import edu.nyu.acsys.CVC4.CVC4JNI;
import edu.nyu.acsys.CVC4.Expr;
import edu.nyu.acsys.CVC4.ExprManager;
import edu.nyu.acsys.CVC4.Kind;
import edu.nyu.acsys.CVC4.Rational;
import edu.nyu.acsys.CVC4.SmtEngine;
import edu.nyu.acsys.CVC4.Type;

public class LinearArithmetikTest {
	public static void main(String[] args) {
		CVC4JNI.Configuration_getVersionString();
		ExprManager em = new ExprManager();
		SmtEngine smt = new SmtEngine(em);

		smt.setLogic("QF_LIRA"); // Set the logic

		// Prove that if given x (Integer) and y (Real) then
		// the maximum value of y - x is 2/3

		// Types
		Type real = em.realType();
		Type integer = em.integerType();

		// Variables
		Expr x = em.mkVar("x", integer);
		Expr y = em.mkVar("a", real);
		Expr b = em.mkVar("b", integer);

		// Constants
		Expr three = em.mkConst(new Rational(3));
		Expr nullC = em.mkConst(new Rational(0));
		Expr two_thirds = em.mkConst(new Rational(2, 3));

		// Terms
		Expr plus = em.mkExpr(Kind.PLUS, y, b);
		Expr diff = em.mkExpr(Kind.MINUS, y, x);

		// Formulas
		Expr x_geq_3y = em.mkExpr(Kind.EQUAL, x, plus);
		Expr x_leq_y = em.mkExpr(Kind.GT, y, nullC);
		Expr neg2_lt_x = em.mkExpr(Kind.GT, b, nullC);

		Expr assumptions = em.mkExpr(Kind.AND, x_geq_3y, x_leq_y);
		assumptions = em.mkExpr(Kind.AND, assumptions, neg2_lt_x);

		System.out.println("Given the assumptions " + assumptions);
		smt.assertFormula(assumptions);


		smt.push();
		Expr diff_leq_two_thirds = em.mkExpr(Kind.LEQ, diff, two_thirds);
		System.out.println("Prove that " + diff_leq_two_thirds + " with CVC4.");
		System.out.println("CVC4 should report VALID.");
		System.out.println("Result from CVC4 is: " + smt.query(diff_leq_two_thirds));
		smt.pop();

		System.out.println();

		smt.push();
		// Expr diff_is_two_thirds = em.mkExpr(Kind.EQUAL, diff, two_thirds);
		//smt.assertFormula(diff_is_two_thirds);
		System.out.println("Show that the asserts are consistent with ");
		//System.out.println(diff_is_two_thirds + " with CVC4.");
		System.out.println("CVC4 should report SAT.");
		System.out.println("Result from CVC4 is: " + smt.checkSat(em.mkConst(true)));
		smt.pop();

		System.out.println("Thus the maximum value of (y - x) is 2/3.");

	}
}
