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
package gov.nasa.jpf.constraints.extensions;

import java.io.File;
import java.io.FilenameFilter;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.logging.Logger;


/**
 * Provides a loading mechanism for JAR files located in any of the following directory:
 * <ul>
 * <li>the <tt>.jconstrains/extensions</tt> subdirectory of the user's home directory,</li>
 * <li>any directory contained in the <tt>jconstraints.extension.path</tt> <i>system</i> property
 * (separated by the platform-specific path separator),</li>
 * <li>any directory contained in the <tt>JCONSTRAINTS_EXT_PATH</tt> environment variable
 * (separated by the platform-specific path separator).</li>
 * </ul>
 * TODO: System-wide directory?
 * 
 *
 */
public class ExtensionLoader {
	
	private static final Logger LOG = Logger.getLogger("constraints");
	
	private static final class InstanceHolder {
		private static final ExtensionLoader INSTANCE = new ExtensionLoader();
	}
	
	public static ExtensionLoader getInstance() {
		return InstanceHolder.INSTANCE;
	}
	
	private static FilenameFilter JAR_FILTER = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			return name.toLowerCase().endsWith(".jar");
		}
	};
	
	private static void addJARs(File directory, List<File> jarList) {
		if(!directory.isDirectory()) {
			if(directory.isFile()) {
				if(directory.getName().toLowerCase().endsWith(".jar")) {
					jarList.add(directory);
				}
				else {
					LOG.warning("Cannot add file " + directory.getAbsolutePath() + " to jConstraints"
							+ " extension path: not a JAR file or directory");
				}
			}
			else {
				LOG.warning("Cannot add " + directory.getAbsolutePath() + " to jConstraints"
						+ " extension path: not a file or directory");
			}
			return;
		}
		
		Collections.addAll(jarList, directory.listFiles(JAR_FILTER));
	}
	
	private static void addJARsFromPath(String pathSpec, List<File> jarList) {
		pathSpec = pathSpec.trim();
		if(pathSpec.isEmpty()) {
			return;
		}
		
		String[] pathNames = pathSpec.trim().split("\\s*" + File.pathSeparator + "\\s*");
		for(String pathName : pathNames) {
			File f = new File(pathName);
			addJARs(f, jarList);
		}
	}
	
	private static List<File> findExtensionJARs(Properties properties) {
		List<File> result = new ArrayList<>();
		
		File userExtDir = new File(System.getProperty("user.home") + File.separator + ".jconstraints"
				+ File.separator + "extensions");
		
		if(userExtDir.exists()) {
			addJARs(userExtDir, result);
		}
		
		String propExtPath = properties.getProperty("jconstraints.extension.path");
		if(propExtPath != null) {
			addJARsFromPath(propExtPath, result);
		}
		
		String envExtPath = System.getenv("JCONSTRAINTS_EXT_PATH");
		
		if(envExtPath != null) {
			addJARsFromPath(envExtPath, result);
		}
		
		return result;
	}
	
	private static ClassLoader createClassLoader(Properties properties) {
		List<File> jars = findExtensionJARs(properties);
		
		URL[] jarUrls = new URL[jars.size()];
		
		int i = 0;
		for(File jar : jars) {
			LOG.fine("jConstraints extension JAR: " + jar.getAbsolutePath());
			try {
				URL jarUrl = jar.toURI().toURL();
				jarUrls[i++] = jarUrl;
			}
			catch(MalformedURLException ex) {
				LOG.severe("Could not create JAR URL for file " + jar.getAbsolutePath() + ": " + ex.getMessage());
			}
		}
		
		if(i < jarUrls.length) {
			// An exception occured, we need to trim the array
			URL[] trimmed = new URL[i];
			System.arraycopy(jarUrls, 0, trimmed, 0, i);
			jarUrls = trimmed;
		}
		
		return URLClassLoader.newInstance(jarUrls, ExtensionLoader.class.getClassLoader());
	}
	
	private final ClassLoader classLoader;
	
	public ClassLoader getClassLoader() {
		return classLoader;
	}
	
	
	// TODO: Add Properties constructor?
	private ExtensionLoader() {
		this.classLoader = createClassLoader(System.getProperties());
	}
}
