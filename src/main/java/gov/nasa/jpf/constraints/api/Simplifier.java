/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

package gov.nasa.jpf.constraints.api;

/**
 * Interface for Simplifiers
 * 
 * @author falk
 * 
 * @param <T> Expression Types
 */
public interface Simplifier<T> {
   
  public Expression<T> simplify(Expression<T> expr);
  
}
