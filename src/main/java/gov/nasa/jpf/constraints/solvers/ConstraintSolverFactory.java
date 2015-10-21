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
import gov.nasa.jpf.constraints.extensions.ExtensionLoader;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Factory for instantiating constraint solvers
 */
public class ConstraintSolverFactory {
	
	protected static Logger logger = Logger.getLogger("constraints");
	
	
	private static final ConstraintSolverFactory ROOT_FACTORY;
	
	static {
		ROOT_FACTORY = new ConstraintSolverFactory(System.getProperties(), null);
		ROOT_FACTORY.discoverProviders(ExtensionLoader.getInstance());
	}
	
	public static ConstraintSolverFactory getRootFactory() {
		return ROOT_FACTORY;
	}
	

	
	private final Map<String, ConstraintSolverProvider> providers = new HashMap<String, ConstraintSolverProvider>();
	private final Properties config = new Properties();
	private final ConstraintSolverFactory parentFactory;

	
	
	public ConstraintSolverFactory() {
		this(System.getProperties(), ROOT_FACTORY);
	}
	
	public ConstraintSolverFactory(Properties config) {
		this(config, ROOT_FACTORY);
	}

	public ConstraintSolverFactory(Properties config, ConstraintSolverFactory parent) {
		this.config.putAll(config);
		this.parentFactory = parent;
	}

	private Properties effectiveConfig(Properties addConfig) {
		Properties config = new Properties(this.config);
		config.putAll(addConfig);
		return config;
	}
	
	public void registerProvider(ConstraintSolverProvider provider) {
		String[] names = provider.getNames();
		
		for(String name : names)
			registerProvider(name, provider);
	}

	public void registerProvider(String name, ConstraintSolverProvider provider) {
		ConstraintSolverProvider prov = providers.get(name);
		if (prov != null && prov != provider)
			logger.log(Level.WARNING, "Overwriting constraint solver provider with name '{0}'", name);
		providers.put(name, provider);
	}

	
	public void discoverProviders() {
		discoverProviders(ExtensionLoader.getInstance());
	}
	
	public void discoverProviders(ExtensionLoader extLoader) {
		discoverProviders(extLoader.getClassLoader());
	}
	
	public void discoverProviders(ClassLoader classLoader) {
		Enumeration<URL> solverFiles;
		try {
			solverFiles = classLoader.getResources("META-INF/constraints/solvers");
		}
		catch(IOException ex) {
			logger.log(Level.WARNING, "Solver provider discovery failed", ex);
			return;
		}
		
		while(solverFiles.hasMoreElements()) {
			URL url = solverFiles.nextElement();
			
			InputStream is = null;
			
			try {
				is = url.openStream();
			
				BufferedReader r = new BufferedReader(new InputStreamReader(is));
				
				String line;
				while((line = r.readLine()) != null) {
					String content = line.split("#", 2)[0].trim();
					
					if("".equals(content))
						continue;

					
					try {
						ConstraintSolverProvider provider = retrieveProvider(content, classLoader);
						registerProvider(provider);
					}
					catch(IllegalArgumentException ex) {
						logger.log(Level.WARNING, "Could not retrieve constraint solver (provider)", ex);
					}
				}
			}
			catch(IOException ex) {
				logger.log(Level.WARNING, "Error reading file {0}: {1}", new Object[]{url, ex.getMessage()});
			}
			finally {
				if(is != null) {
					try {
						is.close();
					}
					catch(IOException ex) {}
				}
			}
		}
		
	}
	
	private ConstraintSolverProvider retrieveProvider(String providerName, ClassLoader loader) {
		try {
			Class<?> clazz = Class.forName(providerName, true, loader);
			
			if(ConstraintSolverProvider.class.isAssignableFrom(clazz)) {
				Class<? extends ConstraintSolverProvider> cspClazz = clazz.asSubclass(ConstraintSolverProvider.class);
				
				try {
					return cspClazz.newInstance();
				}
				catch(IllegalAccessException ex) {}
				catch(InstantiationException ex) {}
			}
			
			Class<? extends ConstraintSolver> csClazz = clazz.asSubclass(ConstraintSolver.class);
			return new ReflectionSolverProvider(csClazz);
		}
		catch(Exception ex) {
			throw new IllegalArgumentException("'" + providerName + "' does not denote a valid constraint solver (provider)");
		}
	}
	
	protected ConstraintSolverProvider getNamedProvider(String name) {
		ConstraintSolverProvider p = providers.get(name);
		if(p == null && parentFactory != null)
			return parentFactory.getNamedProvider(name);
		return p;
	}

	public ConstraintSolver createSolver(String name, Properties config) {
		return createSolver(name, config, true);
	}
	
	

	public ConstraintSolver createSolver(String name, Properties config,
			boolean useFactoryConfig) {
		
		ConstraintSolverProvider provider = getNamedProvider(name);

		if (useFactoryConfig)
			config = effectiveConfig(config);

		if (provider == null)
			provider = retrieveProvider(name, getClass().getClassLoader());
		
		return provider.createSolver(config);
	}

	public ConstraintSolver createSolver(Properties config) {
		return createSolver(config, true);
	}

	public ConstraintSolver createSolver(Properties config,
			boolean useFactoryConfig) {
		if (useFactoryConfig)
			config = effectiveConfig(config);

		String solver = config.getProperty("symbolic.dp");
	

		return createSolver(solver, config, false);
	
	}

	public ConstraintSolver createSolver() {
		return createSolver(this.config, false);
	}

	public ConstraintSolver createSolver(String name) {
		return createSolver(name, this.config, false);
	}

}
