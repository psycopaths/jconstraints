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

import gov.nasa.jpf.constraints.casts.CastOperation;
import gov.nasa.jpf.constraints.casts.NumericCastOperation;
import gov.nasa.jpf.constraints.exceptions.ImpreciseDoubleException;
import gov.nasa.jpf.constraints.exceptions.ImpreciseRepresentationException;

import java.math.BigDecimal;
import java.math.BigInteger;

public abstract class BuiltinTypes {

	public static final class SInt8Type extends ConcreteBVIntegerType<Byte> {
		SInt8Type() {
			super("sint8",
				  Byte.class,
				  Byte.valueOf((byte) 0),
				  8,
				  true,
				  BigInteger.valueOf(Byte.MIN_VALUE),
				  BigInteger.valueOf(Byte.MAX_VALUE),
				  SINT16,
				  new String[]{"byte"},
				  byte.class);
		}

		@Override
		public Byte parse(final String string) {
			return new BigInteger(string).byteValue();
		}

		@Override
		public int compare(final Byte left, final Byte right) {
			return left.compareTo(right);
		}

		@Override
		public Byte negate(final Byte num) {
			return (byte) -num;
		}

		@Override
		public Byte shiftLeft(final Byte value, final Byte shiftAmt) {
			return (byte) (value << shiftAmt);
		}

		@Override
		public Byte shiftRight(final Byte value, final Byte shiftAmt) {
			return (byte) (value >> shiftAmt);
		}

		@Override
		public Byte shiftRightUnsigned(final Byte value, final Byte shiftAmt) {
			return (byte) (value >>> shiftAmt);
		}

		@Override
		public Byte not(final Byte value) {
			return (byte) ~value;
		}

		@Override
		public Byte and(final Byte left, final Byte right) {
			return (byte) (left & right);
		}

		@Override
		public Byte or(final Byte left, final Byte right) {
			return (byte) (left | right);
		}

		@Override
		public Byte xor(final Byte left, final Byte right) {
			return (byte) (left ^ right);
		}

		@Override
		public Byte plus(final Byte left, final Byte right) {
			return (byte) (left + right);
		}

		@Override
		public Byte minus(final Byte left, final Byte right) {
			return (byte) (left - right);
		}

		@Override
		public Byte mul(final Byte left, final Byte right) {
			return (byte) (left * right);
		}

		@Override
		public Byte div(final Byte left, final Byte right) {
			return (byte) (left / right);
		}

		@Override
		public Byte mod(final Byte left, final Byte right) {
			return (byte) (left % right);
		}

		@Override
		public BigInteger integerValue(final Byte value) {
			return BigInteger.valueOf(value.intValue());
		}

		@Override
		public Byte cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).byteValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Byte> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Byte>) NumericCastOperation.TO_SINT8;
			}
			return null;
		}
	}

	public static final class SInt16Type extends ConcreteBVIntegerType<Short> {
		SInt16Type() {
			super("sint16",
				  Short.class,
				  (short) 0,
				  16,
				  true,
				  BigInteger.valueOf(Short.MIN_VALUE),
				  BigInteger.valueOf(Short.MAX_VALUE),
				  SINT32,
				  new String[]{"short"},
				  short.class);
		}

		@Override
		public Short parse(final String string) {
			return new BigInteger(string).shortValue();
		}

		@Override
		public int compare(final Short left, final Short right) {
			return left.compareTo(right);
		}

		@Override
		public Short negate(final Short num) {
			return (short) -num;
		}

		@Override
		public Short shiftLeft(final Short value, final Short shiftAmt) {
			return (short) (value << shiftAmt);
		}

		@Override
		public Short shiftRight(final Short value, final Short shiftAmt) {
			return (short) (value >> shiftAmt);
		}

		@Override
		public Short shiftRightUnsigned(final Short value, final Short shiftAmt) {
			return (short) (value >>> shiftAmt);
		}

		@Override
		public Short plus(final Short left, final Short right) {
			return (short) (left + right);
		}

		@Override
		public Short minus(final Short left, final Short right) {
			return (short) (left - right);
		}

		@Override
		public Short mul(final Short left, final Short right) {
			return (short) (left * right);
		}

		@Override
		public Short div(final Short left, final Short right) {
			return (short) (left / right);
		}

		@Override
		public Short mod(final Short left, final Short right) {
			return (short) (left % right);
		}

		@Override
		public Short not(final Short value) {
			return (short) ~value;
		}

		@Override
		public Short and(final Short left, final Short right) {
			return (short) (left & right);
		}

		@Override
		public Short or(final Short left, final Short right) {
			return (short) (left | right);
		}

		@Override
		public Short xor(final Short left, final Short right) {
			return (short) (left ^ right);
		}

		@Override
		public BigInteger integerValue(final Short value) {
			return BigInteger.valueOf(value.longValue());
		}

		@Override
		public Short cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).shortValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Short> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Short>) NumericCastOperation.TO_SINT16;
			}
			return null;
		}
	}

	public static final class UInt16Type extends ConcreteBVIntegerType<Character> {
		UInt16Type() {
			super("uint16",
				  Character.class,
				  Character.valueOf('\0'),
				  16,
				  false,
				  BigInteger.valueOf(Character.MIN_VALUE),
				  BigInteger.valueOf(Character.MAX_VALUE),
				  SINT32,
				  new String[]{"char"},
				  char.class);
		}

		@Override
		public Character shiftLeft(final Character value, final Character shiftAmt) {
			return (char) (value << shiftAmt);
		}

		@Override
		public Character shiftRight(final Character value, final Character shiftAmt) {
			return (char) (value >> shiftAmt);
		}

		@Override
		public Character shiftRightUnsigned(final Character value, final Character shiftAmt) {
			return (char) (value >>> shiftAmt);
		}

		@Override
		public Character not(final Character value) {
			return (char) ~value;
		}

		@Override
		public Character and(final Character left, final Character right) {
			return (char) (left & right);
		}

		@Override
		public Character or(final Character left, final Character right) {
			return (char) (left | right);
		}

		@Override
		public Character xor(final Character left, final Character right) {
			return (char) (left ^ right);
		}

		@Override
		public BigInteger integerValue(final Character value) {
			return BigInteger.valueOf(value);
		}

		@Override
		public int compare(final Character left, final Character right) {
			return left - right;
		}

		@Override
		public Character plus(final Character left, final Character right) {
			return (char) (left + right);
		}

		@Override
		public Character minus(final Character left, final Character right) {
			return (char) (left - right);
		}

		@Override
		public Character mul(final Character left, final Character right) {
			return (char) (left * right);
		}

		@Override
		public Character div(final Character left, final Character right) {
			return (char) (left / right);
		}

		@Override
		public Character mod(final Character left, final Character right) {
			return (char) (left % right);
		}

		@Override
		public Character negate(final Character num) {
			return (char) -num;
		}

		@Override
		public Character cast(final Object other) {
			if (other instanceof Number) {
				return (char) ((Number) other).intValue();
			}
			if (other instanceof Character) {
				return ((Character) other).charValue();
			}
			throw new ClassCastException("Cannot cast from " + other.getClass().getName() + " to char");
		}

		@Override
		public Character parse(final String string) {
			final BigInteger bi = new BigInteger(string);
			return (char) bi.intValue();
		}
	}

	public static final class SInt32Type extends ConcreteBVIntegerType<Integer> {
		SInt32Type() {
			super("sint32",
				  Integer.class,
				  0,
				  32,
				  true,
				  BigInteger.valueOf(Integer.MIN_VALUE),
				  BigInteger.valueOf(Integer.MAX_VALUE),
				  SINT64,
				  new String[]{"int"},
				  int.class);
		}

		@Override
		public Integer parse(final String string) {
			return new BigInteger(string).intValue();
		}

		@Override
		public int compare(final Integer left, final Integer right) {
			return left.compareTo(right);
		}

		@Override
		public Integer negate(final Integer num) {
			return -num;
		}

		@Override
		public Integer shiftLeft(final Integer value, final Integer shiftAmt) {
			return value << shiftAmt;
		}

		@Override
		public Integer shiftRight(final Integer value, final Integer shiftAmt) {
			return value >> shiftAmt;
		}

		@Override
		public Integer shiftRightUnsigned(final Integer value, final Integer shiftAmt) {
			return value >>> shiftAmt;
		}

		@Override
		public Integer plus(final Integer left, final Integer right) {
			return left + right;
		}

		@Override
		public Integer minus(final Integer left, final Integer right) {
			return left - right;
		}

		@Override
		public Integer mul(final Integer left, final Integer right) {
			return left * right;
		}

		@Override
		public Integer div(final Integer left, final Integer right) {
			return left / right;
		}

		@Override
		public Integer mod(final Integer left, final Integer right) {
			return left % right;
		}

		@Override
		public Integer not(final Integer value) {
			return ~value;
		}

		@Override
		public Integer and(final Integer left, final Integer right) {
			return left & right;
		}

		@Override
		public Integer or(final Integer left, final Integer right) {
			return left | right;
		}

		@Override
		public Integer xor(final Integer left, final Integer right) {
			return left ^ right;
		}

		@Override
		public BigInteger integerValue(final Integer value) {
			return BigInteger.valueOf(value.longValue());
		}

		@Override
		public Integer cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).intValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Integer> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Integer>) NumericCastOperation.TO_SINT32;
			}
			return null;
		}
	}

	public static final class SInt64Type extends ConcreteBVIntegerType<Long> {
		SInt64Type() {
			super("sint64",
				  Long.class,
				  0L,
				  64,
				  true,
				  BigInteger.valueOf(Long.MIN_VALUE),
				  BigInteger.valueOf(Long.MAX_VALUE),
				  INTEGER,
				  new String[]{"long"},
				  long.class);
		}

		@Override
		public Long parse(final String string) {
			return new BigInteger(string).longValue();
		}

		@Override
		public int compare(final Long left, final Long right) {
			return left.compareTo(right);
		}

		@Override
		public Long negate(final Long num) {
			return -num;
		}

		@Override
		public Long shiftLeft(final Long value, final Long shiftAmt) {
			return value << shiftAmt;
		}

		@Override
		public Long shiftRight(final Long value, final Long shiftAmt) {
			return value >> shiftAmt;
		}

		@Override
		public Long shiftRightUnsigned(final Long value, final Long shiftAmt) {
			return value >>> shiftAmt;
		}

		@Override
		public Long plus(final Long left, final Long right) {
			return left + right;
		}

		@Override
		public Long minus(final Long left, final Long right) {
			return left - right;
		}

		@Override
		public Long mul(final Long left, final Long right) {
			return left * right;
		}

		@Override
		public Long div(final Long left, final Long right) {
			return left / right;
		}

		@Override
		public Long mod(final Long left, final Long right) {
			return left % right;
		}

		@Override
		public Long not(final Long value) {
			return ~value;
		}

		@Override
		public Long and(final Long left, final Long right) {
			return left & right;
		}

		@Override
		public Long or(final Long left, final Long right) {
			return left | right;
		}

		@Override
		public Long xor(final Long left, final Long right) {
			return left ^ right;
		}

		@Override
		public BigInteger integerValue(final Long value) {
			return BigInteger.valueOf(value.longValue());
		}

		@Override
		public Long cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).longValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Long> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Long>) NumericCastOperation.TO_SINT64;
			}
			return null;
		}
	}

	public static final class FloatType extends ConcreteFloatingPointType<Float> {
		FloatType() {
			super("float",
				  Float.class,
				  0.0f,
				  true,
				  23,
				  BigDecimal.valueOf(-Float.MAX_VALUE),
				  BigDecimal.valueOf(Float.MAX_VALUE),
				  DOUBLE,
				  new String[]{"float32"},
				  float.class);
		}

		@Override
		public Float parse(final String string) {
			return new BigDecimal(string).floatValue();
		}

		@Override
		public int compare(final Float left, final Float right) {
			return left.compareTo(right);
		}

		@Override
		public Float negate(final Float num) {
			return -num;
		}

		@Override
		public Float plus(final Float left, final Float right) {
			return left + right;
		}

		@Override
		public Float minus(final Float left, final Float right) {
			return left - right;
		}

		@Override
		public Float mul(final Float left, final Float right) {
			return left * right;
		}

		@Override
		public Float div(final Float left, final Float right) {
			return left / right;
		}

		@Override
		public Float mod(final Float left, final Float right) {
			return left % right;
		}


		@Override
		public BigDecimal decimalValue(final Float value) {
			return BigDecimal.valueOf(value.doubleValue());
		}

		@Override
		public Float cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).floatValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Float> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Float>) NumericCastOperation.TO_FLOAT;
			}
			return null;
		}
	}

	public static final class DoubleType extends ConcreteFloatingPointType<Double> {
		DoubleType() {
			super("double",
				  Double.class,
				  0.0,
				  true,
				  52,
				  BigDecimal.valueOf(-Double.MAX_VALUE),
				  BigDecimal.valueOf(Double.MAX_VALUE),
				  DECIMAL,
				  new String[]{"float64"},
				  double.class);
		}

		@Override
		public Double parse(final String string) throws ImpreciseRepresentationException {
			BigDecimal original = new BigDecimal(string);
			double d = original.doubleValue();
			BigDecimal test = new BigDecimal(d);
			if (test.compareTo(original) == 0) {
				return new BigDecimal(string).doubleValue();
			} else {
				throw new ImpreciseDoubleException("The BigDecimal value is not expressable as an double");
			}
		}

		@Override
		public int compare(final Double left, final Double right) {
			return left.compareTo(right);
		}

		@Override
		public Double negate(final Double num) {
			return -num;
		}

		@Override
		public Double plus(final Double left, final Double right) {
			return left + right;
		}

		@Override
		public Double minus(final Double left, final Double right) {
			return left - right;
		}

		@Override
		public Double mul(final Double left, final Double right) {
			return left * right;
		}

		@Override
		public Double div(final Double left, final Double right) {
			return left / right;
		}

		@Override
		public Double mod(final Double left, final Double right) {
			return left % right;
		}

		@Override
		public BigDecimal decimalValue(final Double value) {
			return BigDecimal.valueOf(value.doubleValue());
		}

		@Override
		public Double cast(final Object other) {
			if (other instanceof Number) {
				return ((Number) other).doubleValue();
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends Double> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends Double>) NumericCastOperation.TO_DOUBLE;
			}
			return null;
		}
	}

	public static final class BigIntegerType extends ConcreteIntegerType<BigInteger> {
		BigIntegerType() {
			super("integer", BigInteger.class, BigInteger.ZERO, true, null, null, DECIMAL, new String[]{"BigInteger"});
		}

		@Override
		public BigInteger parse(final String string) {
			return new BigInteger(string);
		}

		@Override
		public int compare(final BigInteger left, final BigInteger right) {
			return left.compareTo(right);
		}

		@Override
		public BigInteger negate(final BigInteger num) {
			return num.negate();
		}

		@Override
		public BigInteger plus(final BigInteger left, final BigInteger right) {
			return left.add(right);
		}

		@Override
		public BigInteger minus(final BigInteger left, final BigInteger right) {
			return left.add(right);
		}

		@Override
		public BigInteger mul(final BigInteger left, final BigInteger right) {
			return left.multiply(right);
		}

		@Override
		public BigInteger div(final BigInteger left, final BigInteger right) {
			return left.divide(right);
		}

		@Override
		public BigInteger mod(final BigInteger left, final BigInteger right) {
			return left.remainder(right);
		}

		@Override
		public BigInteger integerValue(final BigInteger value) {
			return value;
		}

		@Override
		public BigInteger cast(final Object other) {
			if (other instanceof BigInteger) {
				return (BigInteger) other;
			}
			if (other instanceof BigDecimal) {
				return ((BigDecimal) other).toBigInteger();
			}
			if (other instanceof Number) {
				return BigInteger.valueOf(((Number) other).longValue());
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends BigInteger> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends BigInteger>) NumericCastOperation.TO_INTEGER;
			}
			return null;
		}
	}

	public static final class BigDecimalType extends ConcreteRealType<BigDecimal> {
		BigDecimalType() {
			super("decimal", BigDecimal.class, BigDecimal.ZERO, true, null, null, null, new String[]{"BigDecimal"});
		}

		@Override
		public BigDecimal parse(final String string) {
			return new BigDecimal(string);
		}

		@Override
		public int compare(final BigDecimal left, final BigDecimal right) {
			return left.compareTo(right);
		}

		@Override
		public BigDecimal negate(final BigDecimal num) {
			return num.negate();
		}

		@Override
		public BigDecimal plus(final BigDecimal left, final BigDecimal right) {
			return left.add(right);
		}

		@Override
		public BigDecimal minus(final BigDecimal left, final BigDecimal right) {
			return left.subtract(right);
		}

		@Override
		public BigDecimal mul(final BigDecimal left, final BigDecimal right) {
			return left.multiply(right);
		}

		@Override
		public BigDecimal div(final BigDecimal left, final BigDecimal right) {
			return left.divide(right);
		}

		@Override
		public BigDecimal mod(final BigDecimal left, final BigDecimal right) {
			return left.remainder(right);
		}

		@Override
		public BigDecimal decimalValue(final BigDecimal value) {
			return value;
		}

		@Override
		public BigDecimal cast(final Object other) {
			if (other instanceof BigDecimal) {
				return (BigDecimal) other;
			}
			if (other instanceof BigInteger) {
				return new BigDecimal((BigInteger) other);
			}
			if (other instanceof Number) {
				return BigDecimal.valueOf(((Number) other).doubleValue());
			}
			throw new ClassCastException();
		}

		@Override
		@SuppressWarnings("unchecked")
		protected <O> CastOperation<? super O, ? extends BigDecimal> castFrom(final Type<O> other) {
			if (Number.class.isAssignableFrom(other.getCanonicalClass())) {
				return (CastOperation<? super O, ? extends BigDecimal>) NumericCastOperation.TO_DECIMAL;
			}
			return null;
		}
	}

	public static final class BoolType extends ConcreteType<Boolean> {
		BoolType() {
			super("bool", Boolean.class, false, null, new String[]{"boolean"}, boolean.class);
		}

		@Override
		public Boolean parse(final String string) {
			return Boolean.parseBoolean(string);
		}

		@Override
		public Boolean cast(final Object other) {
			if (other instanceof Boolean) {
				return (Boolean) other;
			}
			throw new ClassCastException();
		}
	}
	
	public static final class RegExType extends ConcreteType<String>{
		RegExType(){
			super("string",String.class,"",null, new String[] {"string"},String.class);
		}

		@Override
		public String cast(Object other) {
			if(other instanceof String) {
				return (String) other;
			}
			throw new ClassCastException();
		}

		@Override
		public String parse(String string){
			return string;
		}
	}
	
	public static final class StringType extends ConcreteType<String>{
		StringType(){
			super("string",String.class,"",null, new String[] {"string"},String.class);
		}

		@Override
		public String cast(Object other) {
			if(other instanceof String) {
				return (String) other;
			}
			throw new ClassCastException();
		}

		@Override
		public String parse(String string){
			return string;
		}
	}
	public static final RegExType REGEX = new RegExType();
	public static final StringType STRING = new StringType();
	public static final BoolType BOOL = new BoolType();
	public static final BigDecimalType DECIMAL = new BigDecimalType();
	public static final BigIntegerType INTEGER = new BigIntegerType();
	public static final DoubleType DOUBLE = new DoubleType();
	public static final FloatType FLOAT = new FloatType();
	public static final SInt64Type SINT64 = new SInt64Type();
	public static final SInt32Type SINT32 = new SInt32Type();
	public static final SInt16Type SINT16 = new SInt16Type();
	public static final UInt16Type UINT16 = new UInt16Type();
	public static final SInt8Type SINT8 = new SInt8Type();

	public static boolean isBuiltinType(final Type aType) {
		if (aType instanceof BoolType || aType instanceof BigDecimalType || aType instanceof BigIntegerType ||
			aType instanceof DoubleType || aType instanceof FloatType || aType instanceof SInt64Type ||
			aType instanceof SInt32Type || aType instanceof SInt16Type || aType instanceof UInt16Type ||
			aType instanceof SInt8Type || aType instanceof RegExType || aType instanceof StringType) {
			return true;
		} else {
			return false;
		}
	}

	static final Type<?>[] BUILTIN_TYPES =
			new Type<?>[]{STRING, REGEX,BOOL, DECIMAL, INTEGER, DOUBLE, FLOAT, SINT64, SINT32, SINT16, UINT16, SINT8};

	private BuiltinTypes() {
	}

}
