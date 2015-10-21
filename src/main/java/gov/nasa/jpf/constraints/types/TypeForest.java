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

package gov.nasa.jpf.constraints.types;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

class TypeForest {
	
	private static final Map<Type<?>,Node> knownTypes
		= new HashMap<Type<?>,Node>();
	private static final Set<Type<?>> pending
		= new HashSet<Type<?>>();
	
	public static class Node {
		private final Type<?> type;
		private final Node parent;
		private final int level;
		
		public Node(Type<?> type, Node parent) {
			this.type = type;
			this.parent = parent;
			this.level = (parent == null) ? 0 : parent.getLevel() + 1;
		}
		
		public int getLevel() {
			return level;
		}
		
		public Node getParent() {
			return parent;
		}
		
		public Type<?> getType() {
			return type;
		}
	}
	
	
	public static Node findCommonAncestor(Node a, Node b) {
		if(a.getLevel() > b.getLevel()) {
			Node tmp = a;
			a = b;
			b = tmp;
		}
		
		while(a.getLevel() < b.getLevel())
			b = b.getParent();
		
		while(a != null) {
			if(a.equals(b))
				return a;
			
			a = a.getParent();
			b = b.getParent();
		}
		
		return null;
	}
	
	private static Node findNodeDirect(Type<?> type) {
		Node n = knownTypes.get(type);
		
		if(n != null)
			return n;
		
		if(!pending.add(type))
			throw new IllegalStateException("Circular supertype dependency!");
		
		Type<?> superType = type.getSuperType();
		
		Node parent = null;
		if(superType != null)
			parent = findNodeDirect(superType);
		
		knownTypes.put(type, n = new Node(type, parent));
		
		return n;
	}
	
	public static Node findNode(Type<?> type) {
		Node n = knownTypes.get(type);
		
		if(n != null)
			return n;
		
		synchronized(knownTypes) {
			return findNodeDirect(type);
		}
	}
	
}
