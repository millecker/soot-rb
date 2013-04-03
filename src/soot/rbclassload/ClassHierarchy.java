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
import soot.coffi.HierarchySootClass;

public class ClassHierarchy {

  private Map<String, HierarchySootClass> m_hierarchySootClasses;
  private Map<String, HierarchyGraph> m_hierarchyGraphs;
  private Set<String> m_roots;
  private Set<HierarchyGraph> m_hierarchyFlyweights;

  public ClassHierarchy(){
    m_hierarchySootClasses = new HashMap<String, HierarchySootClass>();
    m_hierarchyGraphs = new HashMap<String, HierarchyGraph>();
    m_hierarchyFlyweights = new HashSet<HierarchyGraph>();
  }

  public void put(String name, HierarchySootClass hierarchy_class){
    m_hierarchySootClasses.put(name, hierarchy_class);
  }

  public void build(){
    //find roots
    m_roots = new HashSet<String>();
    m_roots.addAll(m_hierarchySootClasses.keySet());

    Iterator<String> all_classes = m_hierarchySootClasses.keySet().iterator();
    while(all_classes.hasNext()){
      String class_name = all_classes.next();
      HierarchySootClass hsoot_class = m_hierarchySootClasses.get(class_name);
      m_roots.remove(hsoot_class.getSuperClass());
      for(String iface : hsoot_class.getInterfaces()){
        m_roots.remove(iface);
      }
    }

    //foreach root
    for(String root : m_roots){    
      //build flyweight HierarchyGraph
      HierarchyGraph hgraph = new HierarchyGraph();
      m_hierarchyFlyweights.add(hgraph);
      List<String> queue = new LinkedList<String>();
      queue.add(root);

      while(queue.isEmpty() == false){
        String curr_class = queue.get(0);
        queue.remove(0);

        //fill m_hierarchyGraphs
        m_hierarchyGraphs.put(curr_class, hgraph);

        HierarchySootClass hclass = m_hierarchySootClasses.get(curr_class);
        if(hclass == null){
          System.out.println("hclass == null");
          System.out.println("  curr_class: "+curr_class);
          continue;
        }

        if(hclass.hasSuperClass()){
          String super_class = hclass.getSuperClass();
          hgraph.addSuperClass(curr_class, super_class);
          queue.add(super_class);
        }

        for(String iface : hclass.getInterfaces()){
          hgraph.addInterface(curr_class, iface);
          queue.add(iface);
        }
      }
    }
  }

  @Override
  public String toString(){
    StringBuilder ret = new StringBuilder();    
    for(HierarchyGraph hgraph : m_hierarchyFlyweights){
      ret.append(hgraph.toString());
    }
    return ret.toString();
  }
}

