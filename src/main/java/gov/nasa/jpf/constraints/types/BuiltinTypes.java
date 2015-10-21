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

import java.math.BigDecimal;
import java.math.BigInteger;

public abstract class BuiltinTypes {
  
  public static final class SInt8Type extends ConcreteBVIntegerType<Byte> {
    SInt8Type() {
      super("sint8", Byte.class, Byte.valueOf((byte)0), 8, true, BigInteger.valueOf(Byte.MIN_VALUE), BigInteger.valueOf(Byte.MAX_VALUE), SINT16, new String[]{"byte"}, byte.class);
    }

    @Override
    public Byte parse(String string) {
      return new BigInteger(string).byteValue();
    }

    @Override
    public int compare(Byte left, Byte right) {
      return left.compareTo(right);
    }

    @Override
    public Byte negate(Byte num) {
      return (byte)-num;
    }

    @Override
    public Byte shiftLeft(Byte value, Byte shiftAmt) {
      return (byte)(value << shiftAmt);
    }

    @Override
    public Byte shiftRight(Byte value, Byte shiftAmt) {
      return (byte)(value >> shiftAmt);
    }

    @Override
    public Byte shiftRightUnsigned(Byte value, Byte shiftAmt) {
      return (byte)(value >>> shiftAmt);
    }

    @Override
    public Byte not(Byte value) {
      return (byte)~value;
    }

    @Override
    public Byte and(Byte left, Byte right) {
      return (byte)(left & right);
    }

    @Override
    public Byte or(Byte left, Byte right) {
      return (byte)(left | right);
    }

    @Override
    public Byte xor(Byte left, Byte right) {
      return (byte)(left ^ right);
    }

    @Override
    public Byte plus(Byte left, Byte right) {
      return (byte)(left + right);
    }

    @Override
    public Byte minus(Byte left, Byte right) {
      return (byte)(left - right);
    }

    @Override
    public Byte mul(Byte left, Byte right) {
      return (byte)(left * right);
    }

    @Override
    public Byte div(Byte left, Byte right) {
      return (byte)(left / right);
    }

    @Override
    public Byte mod(Byte left, Byte right) {
      return (byte)(left % right);
    }

    @Override
    public BigInteger integerValue(Byte value) {
      return BigInteger.valueOf(value.intValue());
    }

    @Override
    public Byte cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).byteValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Byte> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Byte>)NumericCastOperation.TO_SINT8;
      return null;
    }
  }

  public static final class SInt16Type extends ConcreteBVIntegerType<Short> {
    SInt16Type() {
      super("sint16", Short.class, (short)0, 16, true, BigInteger.valueOf(Short.MIN_VALUE), BigInteger.valueOf(Short.MAX_VALUE), SINT32, new String[]{"short"}, short.class);
    }

    @Override
    public Short parse(String string) {
      return new BigInteger(string).shortValue();
    }

    @Override
    public int compare(Short left, Short right) {
      return left.compareTo(right);
    }

    @Override
    public Short negate(Short num) {
      return (short)-num;
    }

    @Override
    public Short shiftLeft(Short value, Short shiftAmt) {
      return (short)(value << shiftAmt);
    }

    @Override
    public Short shiftRight(Short value, Short shiftAmt) {
      return (short)(value >> shiftAmt);
    }

    @Override
    public Short shiftRightUnsigned(Short value, Short shiftAmt) {
      return (short)(value >>> shiftAmt);
    }

    @Override
    public Short plus(Short left, Short right) {
      return (short)(left + right);
    }

    @Override
    public Short minus(Short left, Short right) {
      return (short)(left - right);
    }

    @Override
    public Short mul(Short left, Short right) {
      return (short)(left * right);
    }

    @Override
    public Short div(Short left, Short right) {
      return (short)(left / right);
    }

    @Override
    public Short mod(Short left, Short right) {
      return (short)(left % right);
    }

    @Override
    public Short not(Short value) {
      return (short)~value;
    }

    @Override
    public Short and(Short left, Short right) {
      return (short)(left & right);
    }

    @Override
    public Short or(Short left, Short right) {
      return (short)(left | right);
    }

    @Override
    public Short xor(Short left, Short right) {
      return (short)(left ^ right);
    }

    @Override
    public BigInteger integerValue(Short value) {
      return BigInteger.valueOf(value.longValue());
    }

    @Override
    public Short cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).shortValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Short> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Short>)NumericCastOperation.TO_SINT16;
      return null;
    }
  }
  
  public static final class UInt16Type extends ConcreteBVIntegerType<Character> {
    UInt16Type() {
      super("uint16", Character.class, Character.valueOf('\0'), 16, false, BigInteger.valueOf(Character.MIN_VALUE), BigInteger.valueOf(Character.MAX_VALUE), SINT32, new String[]{"char"}, char.class);
    }

    @Override
    public Character shiftLeft(Character value, Character shiftAmt) {
      return (char)(value << shiftAmt);
    }

    @Override
    public Character shiftRight(Character value, Character shiftAmt) {
      return (char)(value >> shiftAmt);
    }

    @Override
    public Character shiftRightUnsigned(Character value, Character shiftAmt) {
      return (char)(value >>> shiftAmt);
    }

    @Override
    public Character not(Character value) {
      return (char)~value;
    }

    @Override
    public Character and(Character left, Character right) {
      return (char)(left & right);
    }

    @Override
    public Character or(Character left, Character right) {
      return (char)(left | right);
    }

    @Override
    public Character xor(Character left, Character right) {
      return (char)(left ^ right);
    }

    @Override
    public BigInteger integerValue(Character value) {
      return BigInteger.valueOf(value);
    }

    @Override
    public int compare(Character left, Character right) {
      return left - right;
    }

    @Override
    public Character plus(Character left, Character right) {
      return (char)(left + right);
    }

    @Override
    public Character minus(Character left, Character right) {
      return (char)(left - right);
    }

    @Override
    public Character mul(Character left, Character right) {
      return (char)(left * right);
    }

    @Override
    public Character div(Character left, Character right) {
      return (char)(left / right);
    }

    @Override
    public Character mod(Character left, Character right) {
      return (char)(left % right);
    }

    @Override
    public Character negate(Character num) {
      return (char)-num;
    }

    @Override
    public Character cast(Object other) {
      if(other instanceof Number)
        return (char)((Number)other).intValue();
      if(other instanceof Character)
        return ((Character)other).charValue();
      throw new ClassCastException("Cannot cast from " + other.getClass().getName() + " to char");
    }

    @Override
    public Character parse(String string) {
      BigInteger bi = new BigInteger(string);
      return (char)bi.intValue();
    }
  }

  public static final class SInt32Type extends ConcreteBVIntegerType<Integer> {
    SInt32Type() {
      super("sint32", Integer.class, 0, 32, true, BigInteger.valueOf(Integer.MIN_VALUE), BigInteger.valueOf(Integer.MAX_VALUE), SINT64, new String[]{"int"}, int.class); 
    }

    @Override
    public Integer parse(String string) {
      return new BigInteger(string).intValue();
    }

    @Override
    public int compare(Integer left, Integer right) {
      return left.compareTo(right);
    }

    @Override
    public Integer negate(Integer num) {
      return -num;
    }

    @Override
    public Integer shiftLeft(Integer value, Integer shiftAmt) {
      return value << shiftAmt;
    }

    @Override
    public Integer shiftRight(Integer value, Integer shiftAmt) {
      return value >> shiftAmt;
    }

    @Override
    public Integer shiftRightUnsigned(Integer value, Integer shiftAmt) {
      return value >>> shiftAmt;
    }

    @Override
    public Integer plus(Integer left, Integer right) {
      return left + right;
    }

    @Override
    public Integer minus(Integer left, Integer right) {
      return left - right;
    }

    @Override
    public Integer mul(Integer left, Integer right) {
      return left * right;
    }

    @Override
    public Integer div(Integer left, Integer right) {
      return left / right;
    }

    @Override
    public Integer mod(Integer left, Integer right) {
      return left % right;
    }

    @Override
    public Integer not(Integer value) {
      return ~value;
    }

    @Override
    public Integer and(Integer left, Integer right) {
      return left & right;
    }

    @Override
    public Integer or(Integer left, Integer right) {
      return left | right;
    }

    @Override
    public Integer xor(Integer left, Integer right) {
      return left ^ right;
    }

    @Override
    public BigInteger integerValue(Integer value) {
      return BigInteger.valueOf(value.longValue());
    }

    @Override
    public Integer cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).intValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Integer> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Integer>)NumericCastOperation.TO_SINT32;
      return null;
    }
  }

  public static final class SInt64Type extends ConcreteBVIntegerType<Long> {
    SInt64Type() {
      super("sint64", Long.class, 0L, 64, true, BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE), INTEGER, new String[]{"long"}, long.class);
    }

    @Override
    public Long parse(String string) {
      return new BigInteger(string).longValue();
    }

    @Override
    public int compare(Long left, Long right) {
      return left.compareTo(right);
    }

    @Override
    public Long negate(Long num) {
      return -num;
    }

    @Override
    public Long shiftLeft(Long value, Long shiftAmt) {
      return value << shiftAmt;
    }

    @Override
    public Long shiftRight(Long value, Long shiftAmt) {
      return value >> shiftAmt;
    }

    @Override
    public Long shiftRightUnsigned(Long value, Long shiftAmt) {
      return value >>> shiftAmt;
    }

    @Override
    public Long plus(Long left, Long right) {
      return left + right;
    }

    @Override
    public Long minus(Long left, Long right) {
      return left - right;
    }

    @Override
    public Long mul(Long left, Long right) {
      return left * right;
    }

    @Override
    public Long div(Long left, Long right) {
      return left / right;
    }

    @Override
    public Long mod(Long left, Long right) {
      return left % right;
    }

    @Override
    public Long not(Long value) {
      return ~value;
    }

    @Override
    public Long and(Long left, Long right) {
      return left & right;
    }

    @Override
    public Long or(Long left, Long right) {
      return left | right;
    }

    @Override
    public Long xor(Long left, Long right) {
      return left ^ right;
    }

    @Override
    public BigInteger integerValue(Long value) {
      return BigInteger.valueOf(value.longValue());
    }

    @Override
    public Long cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).longValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Long> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Long>)NumericCastOperation.TO_SINT64;
      return null;
    }
  }

  public static final class FloatType extends ConcreteFloatingPointType<Float> {
    FloatType() {
      super("float", Float.class, 0.0f, true, 23, BigDecimal.valueOf(-Float.MAX_VALUE), BigDecimal.valueOf(Float.MAX_VALUE), DOUBLE, new String[]{"float32"}, float.class);
    }

    @Override
    public Float parse(String string) {
      return new BigDecimal(string).floatValue();
    }

    @Override
    public int compare(Float left, Float right) {
      return left.compareTo(right);
    }

    @Override
    public Float negate(Float num) {
      return -num;
    }

    @Override
    public Float plus(Float left, Float right) {
      return left + right;
    }

    @Override
    public Float minus(Float left, Float right) {
      return left - right;
    }

    @Override
    public Float mul(Float left, Float right) {
      return left * right;
    }

    @Override
    public Float div(Float left, Float right) {
      return left / right;
    }

    @Override
    public Float mod(Float left, Float right) {
      return left % right;
    }


    @Override
    public BigDecimal decimalValue(Float value) {
      return BigDecimal.valueOf(value.doubleValue());
    }

    @Override
    public Float cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).floatValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Float> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Float>)NumericCastOperation.TO_FLOAT;
      return null;
    }
  }

  public static final class DoubleType extends ConcreteFloatingPointType<Double> {
    DoubleType() {
      super("double", Double.class, 0.0, true, 52, BigDecimal.valueOf(-Double.MAX_VALUE), BigDecimal.valueOf(Double.MAX_VALUE), DECIMAL, new String[]{"float64"}, double.class);
    }

    @Override
    public Double parse(String string) {
      return new BigDecimal(string).doubleValue();
    }

    @Override
    public int compare(Double left, Double right) {
      return left.compareTo(right);
    }

    @Override
    public Double negate(Double num) {
      return -num;
    }

    @Override
    public Double plus(Double left, Double right) {
      return left + right;
    }

    @Override
    public Double minus(Double left, Double right) {
      return left - right;
    }

    @Override
    public Double mul(Double left, Double right) {
      return left * right;
    }

    @Override
    public Double div(Double left, Double right) {
      return left / right;
    }

    @Override
    public Double mod(Double left, Double right) {
      return left % right;
    }

    @Override
    public BigDecimal decimalValue(Double value) {
      return BigDecimal.valueOf(value.doubleValue());
    }

    @Override
    public Double cast(Object other) {
      if(other instanceof Number)
        return ((Number)other).doubleValue();
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends Double> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends Double>)NumericCastOperation.TO_DOUBLE;
      return null;
    }
  }

  public static final class BigIntegerType extends ConcreteIntegerType<BigInteger> {
    BigIntegerType() {
      super("integer", BigInteger.class, BigInteger.ZERO, true, null, null, DECIMAL, new String[]{"BigInteger"});
    }

    @Override
    public BigInteger parse(String string) {
      return new BigInteger(string);
    }

    @Override
    public int compare(BigInteger left, BigInteger right) {
      return left.compareTo(right);
    }

    @Override
    public BigInteger negate(BigInteger num) {
      return num.negate();
    }

    @Override
    public BigInteger plus(BigInteger left, BigInteger right) {
      return left.add(right);
    }

    @Override
    public BigInteger minus(BigInteger left, BigInteger right) {
      return left.add(right);
    }

    @Override
    public BigInteger mul(BigInteger left, BigInteger right) {
      return left.multiply(right);
    }

    @Override
    public BigInteger div(BigInteger left, BigInteger right) {
      return left.divide(right);
    }

    @Override
    public BigInteger mod(BigInteger left, BigInteger right) {
      return left.remainder(right);
    }

    @Override
    public BigInteger integerValue(BigInteger value) {
      return value;
    }

    @Override
    public BigInteger cast(Object other) {
      if(other instanceof BigInteger)
        return (BigInteger)other;
      if(other instanceof BigDecimal)
        return ((BigDecimal)other).toBigInteger();
      if(other instanceof Number)
        return BigInteger.valueOf(((Number)other).longValue());
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends BigInteger> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends BigInteger>)NumericCastOperation.TO_INTEGER;
      return null;
    }
  }

  public static final class BigDecimalType extends ConcreteRealType<BigDecimal> {
    BigDecimalType() {
      super("decimal", BigDecimal.class, BigDecimal.ZERO, true, null, null, null, new String[]{"BigDecimal"});
    }

    @Override
    public BigDecimal parse(String string) {
      return new BigDecimal(string);
    }

    @Override
    public int compare(BigDecimal left, BigDecimal right) {
      return left.compareTo(right);
    }

    @Override
    public BigDecimal negate(BigDecimal num) {
      return num.negate();
    }

    @Override
    public BigDecimal plus(BigDecimal left, BigDecimal right) {
      return left.add(right);
    }

    @Override
    public BigDecimal minus(BigDecimal left, BigDecimal right) {
      return left.subtract(right);
    }

    @Override
    public BigDecimal mul(BigDecimal left, BigDecimal right) {
      return left.multiply(right);
    }

    @Override
    public BigDecimal div(BigDecimal left, BigDecimal right) {
      return left.divide(right);
    }

    @Override
    public BigDecimal mod(BigDecimal left, BigDecimal right) {
      return left.remainder(right);
    }

    @Override
    public BigDecimal decimalValue(BigDecimal value) {
      return value;
    }

    @Override
    public BigDecimal cast(Object other) {
      if(other instanceof BigDecimal)
        return (BigDecimal)other;
      if(other instanceof BigInteger)
        return new BigDecimal((BigInteger)other);
      if(other instanceof Number)
        return BigDecimal.valueOf(((Number)other).doubleValue());
      throw new ClassCastException();
    }
    
    @Override
    @SuppressWarnings("unchecked")
    protected <O> CastOperation<? super O, ? extends BigDecimal> castFrom(
        Type<O> other) {
      if(Number.class.isAssignableFrom(other.getCanonicalClass()))
        return (CastOperation<? super O,? extends BigDecimal>)NumericCastOperation.TO_DECIMAL;
      return null;
    }
  }

  public static final class BoolType extends ConcreteType<Boolean> {
    BoolType() {
      super("bool", Boolean.class, false, null, new String[]{"boolean"}, boolean.class);
    }

    @Override
    public Boolean parse(String string) {
      return Boolean.parseBoolean(string);
    }

    @Override
    public Boolean cast(Object other) {
      if(other instanceof Boolean)
        return (Boolean)other;
      throw new ClassCastException();
    }
  }

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
  
  static final Type<?>[] BUILTIN_TYPES = new Type<?>[]{
    BOOL,
    DECIMAL,
    INTEGER,
    DOUBLE,
    FLOAT,
    SINT64,
    SINT32,
    SINT16,
    UINT16,
    SINT8
  };

  private BuiltinTypes() {}

}
