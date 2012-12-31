/* Soot - a J*va Optimization Framework
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

/* The soot.rbclassload package is:
 * Copyright (C) 2012 Phil Pratt-Szeliga
 * Copyright (C) 2012 Marc-Andre Laverdiere-Papineau
 */

package soot.rbclassload;

import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

public class StringCallGraph {

  private Map<String, Set<String>> m_forwardEdges;
  private Map<String, Set<String>> m_reverseEdges;

  public StringCallGraph(){
    m_forwardEdges = new HashMap<String, Set<String>>();
    m_reverseEdges = new HashMap<String, Set<String>>();
  }

  public void addEdge(String source_sig, String dest_sig){
    addEdge(m_forwardEdges, source_sig, dest_sig);
    addEdge(m_reverseEdges, dest_sig, source_sig); 
  }

  private void addEdge(Map<String, Set<String>> map, String key, String value){
    Set<String> targets;
    if(map.containsKey(key)){
      targets = map.get(key);
    } else {
      targets = new HashSet<String>();
      map.put(key, targets);
    }
    if(targets.contains(value) == false){
      targets.add(value);
    }
  }

  public void remapAll(){
    m_forwardEdges = remapAll(m_forwardEdges);
    m_reverseEdges = remapAll(m_reverseEdges);
  } 

  private Map<String, Set<String>> remapAll(Map<String, Set<String>> map){
    Map<String, Set<String>> new_map = new HashMap<String, Set<String>>();
    Iterator<String> iter = map.keySet().iterator();
    while(iter.hasNext()){
      String key = iter.next();
      Set<String> targets = map.get(key);
      for(String target : targets){
        String source = remapSignature(key);     
        String dest = remapSignature(target);
        addEdge(new_map, source, dest);
      }
    }
    return new_map;
  }

  private String remapSignature(String signature){
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);
    util.remap();
    return util.getSignature();
  }

  public Set<String> getReverseEdges(String dest_sig){
    return m_reverseEdges.get(dest_sig);
  } 
}
