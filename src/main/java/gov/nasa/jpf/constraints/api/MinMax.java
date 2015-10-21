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
package gov.nasa.jpf.constraints.api;

import java.util.HashMap;
import java.util.Map;

/**
 * This class is legacy API and should not be used.
 */
@Deprecated
@SuppressWarnings({"rawtypes","unchecked"})
public class MinMax {

  private Integer intMin = Integer.MAX_VALUE;
  private Integer intMax = Integer.MIN_VALUE;

  private Double doubleMin = null;
  private Double doubleMax = null;

  private final Map<String, Object> varMin;
  private final Map<String, Object> varMax;
  private final Map<String, String> configVarMin;
  private final Map<String, String> configVarMax;

  public MinMax() {
    this.varMin = new HashMap<String, Object>();
    this.varMax = new HashMap<String, Object>();
    this.configVarMin = new HashMap<String, String>();
    this.configVarMax = new HashMap<String, String>();
  }

  /**
   * copy constructor
   * 
   * @param orig
   */
  public MinMax(MinMax orig) {
    this.intMax = orig.intMax;
    this.intMin = orig.intMin;
    this.doubleMax = orig.doubleMax;
    this.doubleMin = orig.doubleMin;

    this.varMax = new HashMap<String, Object>(orig.varMax);
    this.varMin = new HashMap<String, Object>(orig.varMin);
    this.configVarMax = new HashMap<String, String>(orig.configVarMax);
    this.configVarMin = new HashMap<String, String>(orig.configVarMin);
  }

  public void apply(MinMax other) {
    this.varMax.putAll(other.varMax);
    this.varMin.putAll(other.varMin);
    this.configVarMax.putAll(other.configVarMax);
    this.configVarMin.putAll(other.configVarMin);
  }

  /**
   * @return the intMin
   */
  public Integer getIntMin() {
    return intMin;
  }

  /**
   * @param intMin
   *          the intMin to set
   */
  public void setIntMin(Integer intMin) {
    this.intMin = intMin;
  }

  /**
   * @return the intMax
   */
  public Integer getIntMax() {
    return intMax;
  }

  /**
   * @param intMax
   *          the intMax to set
   */
  public void setIntMax(Integer intMax) {
    this.intMax = intMax;
  }

  /**
   * @return the doubleMin
   */
  public Double getDoubleMin() {
    return doubleMin;
  }

  /**
   * @param doubleMin
   *          the doubleMin to set
   */
  public void setDoubleMin(Double doubleMin) {
    this.doubleMin = doubleMin;
  }

  /**
   * @return the doubleMax
   */
  public Double getDoubleMax() {
    return doubleMax;
  }

  /**
   * @param doubleMax
   *          the doubleMax to set
   */
  public void setDoubleMax(Double doubleMax) {
    this.doubleMax = doubleMax;
  }

  /**
   * @return the varMin
   */
  public Object getVarMin(Variable var) {
    return varMin.get(var.getName());
  }

  /**
   * @param varMin
   *          the varMin to set
   */
  public void setVarMin(Variable var, Object varMin) {
    this.varMin.put(var.getName(), varMin);
  }

  /**
   * @return the varMax
   */
  public Object getVarMax(Variable var) {
    return varMax.get(var.getName());
  }

  /**
   * @param varMax
   *          the varMax to set
   */
  public void setVarMax(Variable var, Object varMax) {
    this.varMax.put(var.getName(), varMax);
  }

  /**
   * @param set
   *          var min as a string
   */
  public void setVarMinAsString(String var, String varMin) {
    this.configVarMin.put(var, varMin);
  }

  /**
   * @param set
   *          var max as a string
   */
  public void setVarMaxAsString(String var, String varMax) {
    this.configVarMax.put(var, varMax);
  }

  /**
   * @return the varMin
   */
  public Object getMin(String name) {
    return varMin.get(name);
  }

  /**
   * @param varMin
   *          the varMin to set
   */
  public void setMin(String name, Object varMin) {
    //logger.fine("Setting min " + name + " " + varMin);
    this.varMin.put(name, varMin);
  }

  /**
   * @return the varMax
   */
  public Object getMax(String name) {
    return varMax.get(name);
  }

  /**
   * @param varMax
   *          the varMax to set
   */
  public void setMax(String name, Object varMax) {
    // logger.fine("Setting max " + name + " " + varMax);
    this.varMax.put(name, varMax);
  }

  /**
   * sets new min only if newMin.compareTo(oldMin) > 0. For Integers, e.g., this
   * means that the new min has to be bigger than the old min.
   * 
   * @param name
   * @param newMin
   */
  public void setMinConditionally(String name, Comparable newMin, Class<?> type) {
    // first set the min value based on any config entries
    String value = this.configVarMin.get(name);
    if (value != null && type != null) {
      if (type == Integer.class) {
        setMin(name, (Integer) Integer.parseInt(value));
      } else if (type == Short.class) {
        setMin(name, (Short) Short.parseShort(value));
      } else if (type == char.class) {
        setMin(name, (char) Integer.parseInt(value) % 256);
      } else if (type == Float.class) {
        setMin(name, (Float) Float.parseFloat(value));
      } else if (type == Double.class) {
        setMin(name, (Double) Double.parseDouble(value));
      }
    }

    // now compare the new min value against the old one and
    // set iff the new one is greater than the old one
    Comparable oldMin = (Comparable) this.varMin.get(name);
    if (oldMin == null || newMin.compareTo(oldMin) > 0) {
      this.setMin(name, newMin);
    }
  }

  /**
   * sets new max only if newMax.compareTo(oldMax) < 0. For Integers, e.g., this
   * means that the new max has to be smaller than the old max.
   * 
   * @param name
   * @param newMax
   */
  public void setMaxConditionally(String name, Comparable newMax, Class<?> type) {
    // first set the max value based on any config entries
    String value = this.configVarMax.get(name);
    if (value != null && type != null) {
      if (type == Integer.class) {
        setMax(name, (Integer) Integer.parseInt(value));
      } else if (type == Short.class) {
        setMax(name, (Short) Short.parseShort(value));
      } else if (type == char.class) {
        setMax(name, (char) Integer.parseInt(value) % 256);
      } else if (type == Float.class) {
        setMax(name, (Float) Float.parseFloat(value));
      } else if (type == Double.class) {
        setMax(name, (Double) Double.parseDouble(value));
      }
    }

    // now set conditionally
    Comparable oldMax = (Comparable) this.varMax.get(name);
    if (oldMax == null || newMax.compareTo(oldMax) < 0) {
      this.setMax(name, newMax);
    }
  }

  public void clear() {
    this.intMin = Integer.MIN_VALUE;
    this.intMax = Integer.MAX_VALUE;
    this.doubleMin = null;
    this.doubleMax = null;
    this.varMax.clear();
    this.varMin.clear();
    this.configVarMax.clear();
    this.configVarMin.clear();
  }

  public void set(MinMax other) {
    this.intMin = other.intMin;
    this.intMax = other.intMax;
    this.doubleMin = other.doubleMin;
    this.doubleMax = other.doubleMax;
    this.varMax.clear();
    this.varMax.putAll(other.varMax);
    this.varMin.clear();
    this.varMin.putAll(other.varMin);
    this.configVarMax.clear();
    this.configVarMax.putAll(other.configVarMax);
    this.configVarMin.clear();
    this.configVarMin.putAll(other.configVarMin);
  }

}
