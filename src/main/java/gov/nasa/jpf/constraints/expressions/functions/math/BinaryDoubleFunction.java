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
package gov.nasa.jpf.constraints.expressions.functions.math;

import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.types.BuiltinTypes;

public abstract class BinaryDoubleFunction extends Function<Double> {

	public BinaryDoubleFunction(String name) {
		super(name, BuiltinTypes.DOUBLE, BuiltinTypes.DOUBLE, BuiltinTypes.DOUBLE);
	}

	@Override
	public Double evaluate(Object... args) {
		if(args.length != 2) {
			throw new IllegalArgumentException("Error evaluating function '" + getName()
					+ "': incorrect number of arguments: expected 1, got " + args.length);
		}
		
		Object arg1 = args[0];
		if(!(arg1 instanceof Number)) {
			throw new IllegalArgumentException("Error evaluating function '" + getName()
					+ "': expected numeric argument, got type " + arg1.getClass());
		}
		
		Object arg2 = args[1];
		if(!(arg2 instanceof Number)) {
			throw new IllegalArgumentException("Error evaluating function '" + getName()
					+ "': expected numeric argument, got type " + arg2.getClass());
		}

                Number narg1 = (Number)arg1;
                Number narg2 = (Number)arg2;
		
		return doEvaluate(narg1.doubleValue(), narg2.doubleValue());
	}

	
	protected abstract double doEvaluate(double v1, double v2);
     
}
