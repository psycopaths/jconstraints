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

package gov.nasa.jpf.constraints.solvers;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.exceptions.SolverCreationException;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;


final class ReflectionSolverProvider implements ConstraintSolverProvider {
	
	private static final Logger logger = Logger.getLogger("constraints");
	
	private final Constructor<? extends ConstraintSolver> ctor;
	private final boolean hasPropertyCtor;
	
	public ReflectionSolverProvider(Class<? extends ConstraintSolver> clazz) {
		Constructor<? extends ConstraintSolver> ctor = null;
		boolean hasPropertyCtor = false;
		
		try {
			ctor = clazz.getConstructor(Properties.class);
			hasPropertyCtor = true;
		}
		catch(NoSuchMethodException ex) {}
		catch(SecurityException ex) {}
		
		if(ctor == null) {
			try {
				ctor = clazz.getConstructor();
			}
			catch(NoSuchMethodException ex) {
				throw new IllegalArgumentException("Constraint solver class " + clazz.getName()
						+ " neither exposes Properties nor default constructor");
			}
			catch(SecurityException ex) {
				throw new IllegalArgumentException("Constraint solver class " + clazz.getName()
						+ " neither exposes Properties nor default constructor");
			}
		}
		
		this.ctor = ctor;
		this.hasPropertyCtor = hasPropertyCtor;
	}
	
	@Override
	public String[] getNames() {
		Class<?> declClazz = ctor.getDeclaringClass();
		return new String[]{declClazz.getSimpleName(), declClazz.getName()};
	}

	@Override
	public ConstraintSolver createSolver(Properties config) {
		try {
			if(hasPropertyCtor)
				return ctor.newInstance(config);
			logger.log(Level.FINE, "Note: {0} does not expose a " +
					"Properties constructor. No configuration is used.", ctor.getDeclaringClass().getName());
			return ctor.newInstance();
		}
		catch(IllegalAccessException ex) {
			throw new SolverCreationException(ex);
		}
		catch(InvocationTargetException ex) {
			throw new SolverCreationException(ex);
		}
		catch(InstantiationException ex) {
			throw new SolverCreationException(ex);
		}
	}

}
