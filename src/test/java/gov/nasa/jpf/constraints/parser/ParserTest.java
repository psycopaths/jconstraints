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

package gov.nasa.jpf.constraints.parser;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.types.TypeContext;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import org.antlr.runtime.RecognitionException;
import org.testng.annotations.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

/**
 *
 */
public class ParserTest {

	@Test(groups = {"parser", "base"})
	public void testParser() throws RecognitionException, ImpreciseRepresentationException {

		TypeContext tc = new TypeContext(true);
		Type dType = tc.byClass(Double.class);
		Type iType = tc.byClass(Integer.class);

		Variable<Double> x1 = new Variable(dType, "x1");
		Variable<Double> x2 = new Variable(dType, "x2");
		Variable<Integer> x3 = new Variable(iType, "x3");

		Collection<Variable<?>> vars = new ArrayList<>();
		Collections.addAll(vars, x1, x2, x3);

		Expression<Boolean> expr = ParserUtil.parseLogical("(x1 * x2 > 10.0) || x3 < 100", tc, vars);

		System.out.println(expr);

		ParserUtil.parseLogical(ExpressionUtil.toParseableString(expr));

		ParserUtil.parseLogical("declare 'i1':sint32 in (forall ('i2':sint32): (('i1' * 'i2') == 0))");

		ParserUtil.parseLogical(
				"declare 'i':sint32, 'this.state':sint32, 'b':bool in (true && (('i' != 'this.state') && 'b'))");

		Valuation val = new Valuation();
		val.setValue(x1, new Double(5));
		val.setValue(x2, new Double(2));
		val.setValue(x3, 1);

		boolean res = (Boolean) expr.evaluate(val);
		System.out.println(res);

		String s = x1.toString(Variable.INCLUDE_VARIABLE_TYPE);
		System.out.println(s);
		System.out.println(ParserUtil.parseVariable(s));

	}

}
