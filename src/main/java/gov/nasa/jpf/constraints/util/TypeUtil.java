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

package gov.nasa.jpf.constraints.util;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.IntegerType;
import gov.nasa.jpf.constraints.types.RealType;

import java.math.BigDecimal;
import java.math.BigInteger;


/**
 * static helpers for dealing with types
 */
public class TypeUtil {
  
  /**
   * real number value
   */
  public static class Real {
    public final BigInteger num;
    public final BigInteger den;
    public final BigInteger pow;

    public Real(BigInteger num, BigInteger den, BigInteger pow) {
      this.num = num;
      this.den = den;
      this.pow = pow;
    }
    
    public Real(BigDecimal d) {
      BigInteger power = BigInteger.ZERO;
      BigInteger div = BigInteger.ONE;
      String dstr = d.toString();
      int indexOfE = dstr.indexOf('E');
      if (indexOfE != -1) {
        power = new BigInteger(dstr.substring(indexOfE + 1));
        dstr = dstr.substring(0, indexOfE);
      }
      int indexOfDot = dstr.indexOf('.');
      if (indexOfDot != -1) {
        int length = dstr.length();
        int nZeroes = length - indexOfDot - 1;
        dstr = dstr.substring(0, indexOfDot) + dstr.substring(indexOfDot + 1, length);
        while (nZeroes > 0) {
          div = div.multiply(BigInteger.TEN);
          nZeroes--;
        }
      }
      this.den = new BigInteger(dstr);
      this.pow = power;
      this.num = div;
    }
    
    public BigDecimal getDecimalValue() {
      return new BigDecimal(num).divide(new BigDecimal(den)).pow(pow.intValue());
    }
  };
  
  
  public static boolean isBoolSort(Expression<?> expression) {
    return expression.getType().equals(BuiltinTypes.BOOL);
  }
  
  public static boolean isIntSort(Expression<?> expression) {
    return (expression.getType() instanceof IntegerType);
  }
  
  public static boolean isRealSort(Expression<?> expression) {
    return (expression.getType() instanceof RealType);
  }
}
