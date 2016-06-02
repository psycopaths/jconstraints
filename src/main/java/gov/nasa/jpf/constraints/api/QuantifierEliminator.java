/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.jpf.constraints.api;

/**
 *
 * @author mmuesly
 */
public interface QuantifierEliminator {
  public Expression eliminateQuantifiers(Expression<Boolean> expr);
}
