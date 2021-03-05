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

package gov.nasa.jpf.constraints.solvers;

import static java.util.Collections.unmodifiableSet;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceConfigurationError;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Looks for available {@code ConstraintSolverProvider} services, instantiates, and saves them for
 * later use.
 */
public final class ConstraintSolverFactory {

  private static final ServiceLoader<ConstraintSolverProvider> loader =
      ServiceLoader.load(ConstraintSolverProvider.class);
  private static final Properties config = new Properties();
  private static final Map<String, ConstraintSolverProvider> providers =
      new HashMap<String, ConstraintSolverProvider>();
  private static final Logger logger = Logger.getLogger("constraints");

  static {
    discoverProviders();
  }

  /**
   * Returns the names of all found {@link ConstraintSolverProvider} services.
   *
   * @return an {@code unmodifiableSet} of names of all found {@code ConstraintSolverProvider}
   *     services
   */
  public static Set<String> getNames() {
    return unmodifiableSet(providers.keySet());
  }

  /**
   * Registers the given {@link ConstraintSolverProvider}. If another provider with the same name is
   * already registered a warning is being logged. It is generally not recommended to register
   * providers manually as the {@code ConstraintSolverService} should discover them automatically.
   * Doing so could create unexpected program-wide side effects.
   *
   * @param newProvider the {@code constraintSolverProvider} to be registered
   */
  public static void registerProvider(ConstraintSolverProvider newProvider) {
    String[] names = newProvider.getNames();
    for (String name : names) {
      ConstraintSolverProvider existingProvider = providers.put(name, newProvider);
      if (existingProvider != null && existingProvider != newProvider) {
        logger.log(Level.WARNING, "Overwriting constraint solver provider with name ''{0}''", name);
      }
    }
  }

  private static void discoverProviders() throws ServiceConfigurationError {
    for (ConstraintSolverProvider solver : loader) {
      for (String foundName : solver.getNames()) {
        providers.put(foundName, solver);
      }
    }
  }

  /**
   * Creates an instance of the {@link ConstraintSolver} with the name {@code name} and the given
   * config. The name is not the name that will be given to the solver, but rather the name which is
   * defined in the {@link ConstraintSolverProvider} of the {@code ConstraintSolver} that should be
   * created. If no {@code ConstraintSolverProvider} with that name is registered a {@code
   * SolverNotFoundException is thrown}. The given {@code properties} object is given to the {@code
   * ConstrainSolver} being created.
   *
   * @see #createSolver(Properties)
   * @see #createSolver(String)
   * @param name a {@code String} containing the name of the {@code ConstraintSolver} that should be
   *     created
   * @param config the {@code properties} object the solver will receive.
   * @return an instance of the specified {@code ConstraintSolver}
   */
  public static ConstraintSolver createSolver(String name, Properties config) {
    ConstraintSolverProvider s = providers.get(name);
    if (s == null) {
      throw new SolverNotFoundExcpetion("Specified solver could not be found");
    } else {
      return s.createSolver(config);
    }
  }

  /**
   * Creates an instance of the {@link ConstraintSolver} specified in the config and also passes the
   * config to the solver. The config has to have the {@code symbolic.dp} property set to the name
   * of the solver that should be created. The name is not the name that will be given to the
   * solver, but rather the name which is defined in the {@link ConstraintSolverProvider} of the
   * {@code ConstraintSolver} that should be created. If no {@code ConstraintSolverProvider} with
   * that name is registered a {@code SolverNotFoundException is thrown}.
   *
   * @see #createSolver(String, Properties)
   * @see #createSolver(String)
   * @param config a {@code properties} object in which at least the {@code symbolic.dp} property is
   *     set to the name of the wanted {@code ConstraintSolver}. The config is also passed to the
   *     solver at creation.
   * @return an instance of the specified {@code ConstraintSolver}
   */
  public static ConstraintSolver createSolver(Properties config) {
    String solver = config.getProperty("symbolic.dp");
    return createSolver(solver, config);
  }

  /**
   * Creates an instance of the {@link ConstraintSolver} with the name {@code name}. The name is not
   * the name that will be given to the solver, but rather the name which is defined in the {@link
   * ConstraintSolverProvider} of the {@code ConstraintSolver} that should be created. If no {@code
   * ConstraintSolverProvider} with that name is registered a {@code SolverNotFoundException is
   * thrown}.
   *
   * @see #createSolver(String, Properties)
   * @see #createSolver(Properties)
   * @param name a {@code String} containing the name of the {@code ConstraintSolver} that should be
   *     created
   * @return an instance of the specified {@code ConstraintSolver}
   */
  public static ConstraintSolver createSolver(String name) {
    return createSolver(name, config);
  }
}
