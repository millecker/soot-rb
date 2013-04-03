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
import java.util.List;
import java.util.ArrayList;

public class HierarchyGraph {

  private Map<String, List<String>> m_parents;
  private Map<String, List<String>> m_children;

  public HierarchyGraph(){
    m_parents = new HashMap<String, List<String>>();
    m_children = new HashMap<String, List<String>>();
  }

  public void addSuperClass(String base_class, String super_class){
    addEdge(m_parents, base_class, super_class);
    addEdge(m_children, super_class, base_class);
  }

  public void addInterface(String base_class, String iface){
    addEdge(m_parents, base_class, iface);
    addEdge(m_children, iface, base_class);
  }

  private void addEdge(Map<String, List<String>> map, String key, String value){
    List<String> values;
    if(map.containsKey(key)){
      values = map.get(key);
    } else {
      values = new ArrayList<String>();
      map.put(key, values);
    }
    values.add(value);
  }

  public List<String> getChildren(String parent){
    if(m_children.containsKey(parent)){
      return m_children.get(parent);
    }
    return new ArrayList<String>();
  }

  public List<String> getParents(String child){
    if(m_parents.containsKey(child)){
      return m_parents.get(child);
    }
    return new ArrayList<String>();
  }

  @Override
  public String toString(){
    StringBuilder ret = new StringBuilder();
    ret.append(printMap(m_parents, "m_parents", "child", "parent"));
    ret.append(printMap(m_children, "m_children", "parent", "child"));
    return ret.toString();
  }

  private String printMap(Map<String, List<String>> map, String heading, String key_name, String value_name){
    StringBuilder ret = new StringBuilder();
    ret.append(heading+"\n");    
    for(String key : map.keySet()){
      List<String> values = map.get(key);
      ret.append("  "+key_name+": "+key+" "+value_name+": "+values.toString()+"\n");
    }
    return ret.toString();
  }
}
