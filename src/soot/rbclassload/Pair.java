/* 
 * Copyright 2012 Phil Pratt-Szeliga and other contributors
 * http://chirrup.org/
 * 
 * See the file LICENSE for copying permission.
 */

package soot.rbclassload;

public class Pair<Key,Value> {
  
  private Key m_key;
  private Value m_value;
  
  public Pair(Key key, Value value){
    m_key = key;
    m_value = value;
  }
  
  public Key getKey(){
    return m_key;
  }
  
  public Value getValue(){
    return m_value;
  }
}
