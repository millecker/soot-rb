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
import java.util.Iterator;
import java.util.List;
import java.util.LinkedList;

public class StringCallGraph {

  private Map<String, Set<String>> m_forwardEdges;
  private Map<String, Set<String>> m_reverseEdges;
  private Set<String> m_allSignatures;
  private Set<String> m_entryPoints;

  public StringCallGraph(){
    m_forwardEdges = new HashMap<String, Set<String>>();
    m_reverseEdges = new HashMap<String, Set<String>>();
    m_allSignatures = new HashSet<String>();
    m_entryPoints = new HashSet<String>();
  }

  public void addEdge(String source_sig, String dest_sig){
    addEdge(m_forwardEdges, source_sig, dest_sig);
    addEdge(m_reverseEdges, dest_sig, source_sig);
    if(m_allSignatures.contains(source_sig) == false){
      m_allSignatures.add(source_sig);
    }
    if(m_allSignatures.contains(dest_sig) == false){
      m_allSignatures.add(dest_sig); 
    }
  }

  public void addEntryPoint(String signature){
    if(m_entryPoints.contains(signature) == false){
      m_entryPoints.add(signature);
    }
  }

  public boolean isReachable(String signature){
    if(m_allSignatures.contains(signature)){
      return true;
    } else {
      return false;
    }
  }

  public int size(){
    return m_allSignatures.size();
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
    String ret = util.getSignature();
    return ret;
  }

  public Set<String> getReverseEdges(String dest_sig){
    if(m_reverseEdges.containsKey(dest_sig)){
      return m_reverseEdges.get(dest_sig);
    } else {
      return new HashSet<String>();
    }
  }

  public Set<String> getForwardEdges(String source_sig){
    if(m_forwardEdges.containsKey(source_sig)){
      return m_forwardEdges.get(source_sig);
    } else {
      return new HashSet<String>();
    }
  }

  @Override
  public String toString(){
    StringBuilder ret = new StringBuilder();
    ret.append("forward edges: \n");
    for(String entry : m_entryPoints){
      List<String> queue = new LinkedList<String>();
      queue.add(entry);
      Set<String> visited = new HashSet<String>();
      while(queue.isEmpty() == false){
        String source = queue.get(0);
        queue.remove(0);

        if(visited.contains(source)){
          continue;
        }
        visited.add(source);
 
        Set<String> targets = getForwardEdges(source);
        for(String target : targets){
          ret.append(source+" -> "+target+"\n");
          queue.add(target);
        }
      }     
    }
    ret.append("reverse edges: \n");
    for(String entry : m_entryPoints){
      List<String> queue = new LinkedList<String>();
      queue.add(entry);
      Set<String> visited = new HashSet<String>();
      while(queue.isEmpty() == false){
        String source = queue.get(0);
        queue.remove(0);

        if(visited.contains(source)){
          continue;
        }
        visited.add(source);
 
        Set<String> targets = getReverseEdges(source);
        for(String target : targets){
          ret.append(target+" -> "+source+"\n");
          queue.add(target);
        }
      }     
    }
    ret.append("entry points: \n");
    for(String entry : m_entryPoints){
      ret.append(entry+"\n");
    }
    return ret.toString();
  } 
}
