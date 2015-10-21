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

import org.antlr.runtime.tree.Tree;

public class UnexpectedTokenException extends ExpressionParseException {
  
  private static final long serialVersionUID = 1L;
  
  private static String tokenNames(int ...expected) {
    StringBuilder sb = new StringBuilder();
    boolean first = true;
    
    for(int i = 0; i < expected.length; i++) {
      int tokId = expected[i];
      String tokName = ExpressionParser.tokenNames[tokId];
      if(first)
        first = false;
      else
        sb.append(',');
      sb.append(tokName);
    }
    
    return sb.toString();
  }
  
  public UnexpectedTokenException(Tree token, int ...expected) {
    super(token.getLine(), token.getCharPositionInLine(), "Encountered token " + ExpressionParser.tokenNames[token.getType()]
        + ", expected " + tokenNames(expected));
    
  }

}
