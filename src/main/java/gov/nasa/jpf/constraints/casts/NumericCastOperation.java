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

import java.math.BigDecimal;
import java.math.BigInteger;

public abstract class NumericCastOperation<T extends Number> implements CastOperation<Number,T> {
	
	private final Class<T> toClass;
	
	public NumericCastOperation(Class<T> toClass) {
		this.toClass = toClass;
	}
	
	public static final NumericCastOperation<Byte> TO_SINT8 = new NumericCastOperation<Byte>(Byte.class) {
		@Override
		public Byte cast(Number from) {
			return from.byteValue();
		}
	};
	public static final NumericCastOperation<Short> TO_SINT16 = new NumericCastOperation<Short>(Short.class) {
		@Override
		public Short cast(Number from) {
			return from.shortValue();
		}
	};
	public static final NumericCastOperation<Integer> TO_SINT32 = new NumericCastOperation<Integer>(Integer.class) {
		@Override
		public Integer cast(Number from) {
			return from.intValue();
		}
	};
	public static final NumericCastOperation<Long> TO_SINT64 = new NumericCastOperation<Long>(Long.class) {
		@Override
		public Long cast(Number from) {
			return from.longValue();
		}
	};
	public static final NumericCastOperation<Float> TO_FLOAT = new NumericCastOperation<Float>(Float.class) {
		@Override
		public Float cast(Number from) {
			return from.floatValue();
		}
	};
	public static final NumericCastOperation<Double> TO_DOUBLE = new NumericCastOperation<Double>(Double.class) {
		@Override
		public Double cast(Number from) {
			return from.doubleValue();
		}
	};
	
	public static final NumericCastOperation<BigInteger> TO_INTEGER = new NumericCastOperation<BigInteger>(BigInteger.class) {
    @Override
    public BigInteger cast(Number from) {
      Class<?> clazz = from.getClass();
      if(clazz == BigInteger.class)
        return (BigInteger)from;
      if(clazz == BigDecimal.class)
        return ((BigDecimal)from).toBigInteger();
      else if(clazz == Double.class || clazz == Float.class)
        return BigDecimal.valueOf(from.doubleValue()).toBigInteger();
      return BigInteger.valueOf(from.longValue());
    }
	};
	
	public static final NumericCastOperation<BigDecimal> TO_DECIMAL = new NumericCastOperation<BigDecimal>(BigDecimal.class) {
    @Override
    public BigDecimal cast(Number from) {
      Class<?> clazz = from.getClass();
      if(clazz == BigDecimal.class)
        return (BigDecimal)from;
      if(clazz == BigInteger.class)
        return new BigDecimal((BigInteger)from);
      if(clazz == Long.class)
        return new BigDecimal(from.longValue());
      return new BigDecimal(from.doubleValue());
    }
	};
	
	public Class<Number> getFromClass() {
		return Number.class;
	}
	
	public Class<T> getToClass() {
		return toClass;
	}
	
}
