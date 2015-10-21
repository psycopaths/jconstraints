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

public class ExpressionParseException extends IllegalArgumentException {
  
  private static final long serialVersionUID = 1L;
  
  private static String createMessage(int line, int col, String message) {
    return "At line " + line + ", column " + col + ": " + message; 
  }

  public ExpressionParseException(int line, int col, String message) {
    super(createMessage(line, col, message));
  }

  public ExpressionParseException(int line, int col, Throwable cause) {
    this(line, col, cause.getMessage(), cause);
  }

  public ExpressionParseException(int line, int col, String message, Throwable cause) {
    super(createMessage(line, col, message), cause);
  }

}
