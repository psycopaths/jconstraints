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

package gov.nasa.jpf.constraints.casts;

public class ClassCastOperation<T> implements CastOperation<Object, T> {
	
	private final Class<T> to;
	
	public ClassCastOperation(Class<T> to) {
		this.to = to;
	}

	@Override
	public T cast(Object from) {
		return to.cast(from);
	}

	@Override
	public Class<Object> getFromClass() {
		return Object.class;
	}

	@Override
	public Class<T> getToClass() {
		return to;
	}

}
