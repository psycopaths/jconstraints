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

public abstract class UnaryDoubleLongFunction extends Function<Long> {

	public UnaryDoubleLongFunction(String name) {
		super(name, BuiltinTypes.SINT64, BuiltinTypes.DOUBLE);
	}

	@Override
	public Long evaluate(Object... args) {
		if(args.length != 1) {
			throw new IllegalArgumentException("Error evaluating function '" + getName()
					+ "': incorrect number of arguments: expected 1, got " + args.length);
		}
		
		Object arg = args[0];
		if(!(arg instanceof Number)) {
			throw new IllegalArgumentException("Error evaluating function '" + getName()
					+ "': expected numeric argument, got type " + arg.getClass());
		}
		
		Number narg = (Number)arg;
		
		return doEvaluate(narg.doubleValue());
	}

	
	protected abstract long doEvaluate(double value);
     
	
	 public static UnaryDoubleLongFunction DOUBLE_TO_LONG_BITS = new UnaryDoubleLongFunction("java.lang.Double.doubleToLongBits") {
	    @Override
	    protected long doEvaluate(double value) {
	      return Double.doubleToLongBits(value);
	    }
	  };     
	
}
