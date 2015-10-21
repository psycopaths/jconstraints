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

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.types.TypeContext;

import java.util.Collection;
import java.util.Collections;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.Tree;

public class ParserUtil {
  
  
  public static Expression<Boolean> parseLogical(String string) throws RecognitionException {
    return parseLogical(string, new TypeContext(true), Collections.<Variable<?>>emptySet());
  }
  
  public static Expression<Boolean> parseLogical(String string, TypeContext types,
    Collection<? extends Variable<?>> variables) throws RecognitionException {
    ExpressionParser parser = getParser(string);
    Tree ast = parser.start().tree;
    ASTTranslator translator = new ASTTranslator(types);
    translator.declareVariables(variables);    
    return translator.translateRootLogical(ast);
  }

  public static Expression parseArithmetic(String string) throws RecognitionException {
    return parseArithmetic(string, new TypeContext(true), Collections.<Variable<?>>emptySet());
  }
  
  public static Expression parseArithmetic(String string, TypeContext types,
    Collection<? extends Variable<?>> variables) throws RecognitionException {
    ExpressionParser parser = getParser(string);
    Tree ast = parser.start_aexpression().tree;
    ASTTranslator translator = new ASTTranslator(types);
    translator.declareVariables(variables);
    return translator.translateRootArithmetic(ast);
  }
  
  public static Variable parseVariable(String string) throws RecognitionException {
    ExpressionParser parser = getParser(string);
    Tree ast = parser.start_variable().tree;
    ASTTranslator translator = new ASTTranslator(new TypeContext(true));
    return translator.translateRootVariable(ast);
  }
  
  private static ExpressionParser getParser(String string) throws RecognitionException {
    CharStream cs = new ANTLRStringStream(string);
    ExpressionLexer lex = new ExpressionLexer(cs);
    TokenStream ts = new CommonTokenStream(lex);
    ExpressionParser parser = new ExpressionParser(ts);
    return parser;
  }

}
