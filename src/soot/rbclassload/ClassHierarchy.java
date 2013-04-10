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
import java.util.ArrayList;

import soot.SootMethod;
import soot.SootClass;
import soot.Scene;
import soot.Type;
import soot.RefType;
import soot.RefLikeType;

public class ClassHierarchy {

  private Map<String, HierarchySootClass> m_hierarchySootClasses;
  private Map<String, List<HierarchyGraph>> m_unmergedGraphs;
  private Map<String, HierarchyGraph> m_hierarchyGraphs;
  private Map<String, List<String>> m_virtualMethodSignatures;
  private Set<String> m_roots;
  private Set<String> m_arrayTypes;
  private List<NumberedType> m_numberedTypes;
  private Map<String, NumberedType> m_numberedTypeMap;
  private MethodSignatureUtil m_util;
  private Map<HierarchySootMethod, HierarchySootMethod> m_virtMap;

  public ClassHierarchy(){
    m_hierarchySootClasses = new HashMap<String, HierarchySootClass>();
    m_hierarchyGraphs = new HashMap<String, HierarchyGraph>();
    m_virtualMethodSignatures = new HashMap<String, List<String>>();
    m_arrayTypes = new HashSet<String>();
    m_numberedTypes = new ArrayList<NumberedType>();
    m_numberedTypeMap = new HashMap<String, NumberedType>();
    m_util = new MethodSignatureUtil();
  }

  public void put(String name, HierarchySootClass hierarchy_class){
    m_hierarchySootClasses.put(name, hierarchy_class);
  }

  public HierarchySootClass getHierarchySootClass(String name){
    return m_hierarchySootClasses.get(name);
  }

  public Set<String> getClasses(){
    return m_hierarchySootClasses.keySet();
  }

  public HierarchySootMethod getHierarchySootMethod(String signature){
    m_util.parse(signature);
    String class_name = m_util.getClassName();
    HierarchySootClass hclass = getHierarchySootClass(class_name);
    if(hclass == null){
      return null;
    }
    return hclass.findMethodBySubSignature(m_util.getSubSignature());
  }

  public boolean containsClass(String name){
    return m_hierarchySootClasses.containsKey(name);
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

    m_unmergedGraphs = new HashMap<String, List<HierarchyGraph>>();

    //foreach root
    for(String root : m_roots){    
      HierarchyGraph hgraph = new HierarchyGraph();
      List<String> queue = new LinkedList<String>();
      queue.add(root);

      while(queue.isEmpty() == false){
        String curr_class = queue.get(0);
        queue.remove(0);

        hgraph.addHierarchyClass(curr_class);

        HierarchySootClass hclass = m_hierarchySootClasses.get(curr_class);
        if(hclass == null){
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

        if(m_hierarchyGraphs.containsKey(curr_class)){
          HierarchyGraph rhs_hgraph = m_hierarchyGraphs.get(curr_class);
          rhs_hgraph.merge(hgraph);
        } else {
          m_hierarchyGraphs.put(curr_class, hgraph); 
        }
      }
    }
  }

  public void addArrayType(String array_type){
    m_arrayTypes.add(array_type);
  }

  public void buildArrayTypes(){
    MultiDimensionalArrayTypeCreator creator = new MultiDimensionalArrayTypeCreator();
    m_arrayTypes = creator.createString(m_arrayTypes);    

    for(String curr_class : m_arrayTypes){
      HierarchyGraph hgraph = new HierarchyGraph();
      hgraph.addHierarchyClass(curr_class);
      hgraph.addSuperClass(curr_class, "java.lang.Object");

      List<HierarchyGraph> graph_list = new ArrayList<HierarchyGraph>();
      graph_list.add(hgraph);

      m_unmergedGraphs.put(curr_class, graph_list);
    }

    mergeGraphs();
  }

  private void mergeGraphs(){
    m_hierarchyGraphs.clear();
    for(String curr_class : m_unmergedGraphs.keySet()){
      List<HierarchyGraph> graphs = m_unmergedGraphs.get(curr_class);
      HierarchyGraph new_graph = new HierarchyGraph();
      for(HierarchyGraph curr_graph : graphs){
        new_graph.merge(curr_graph);
      }
      m_hierarchyGraphs.put(curr_class, new_graph);
    }
  }

  public NumberedType getNumberedType(String str){
    if(m_numberedTypeMap.containsKey(str)){
      return m_numberedTypeMap.get(str);
    } else {
      System.out.println("cannot find numbered type: "+str);
      Iterator<String> iter = m_numberedTypeMap.keySet().iterator();
      while(iter.hasNext()){
        System.out.println("  "+iter.next());
      }      
      System.exit(0);
      return null;
    }
  }

  public void numberTypes(){
    System.out.println("numbering types...");
    int number = 1;
    List<String> queue = new LinkedList<String>();
    Set<String> visited = new HashSet<String>();
    queue.add("java.lang.Object");
    HierarchyGraph hgraph = m_hierarchyGraphs.get("java.lang.Object");

    while(queue.isEmpty() == false){
      String curr_type = queue.get(0);
      queue.remove(0);

      if(visited.contains(curr_type)){
        continue;
      }
      visited.add(curr_type);
      
      List<String> children = hgraph.getChildren(curr_type);
      queue.addAll(children);

      NumberedType numbered_type = new NumberedType(curr_type, number);
      m_numberedTypes.add(numbered_type);
      m_numberedTypeMap.put(curr_type, numbered_type);
      
      number++;
    }
  }

  public List<NumberedType> getNumberedTypes(){
    return m_numberedTypes;
  }

  public void cacheVirtualMethods(){   
    m_virtMap = new HashMap<HierarchySootMethod, HierarchySootMethod>();
    for(String base_class : getClasses()){
      HierarchySootClass base_hclass = getHierarchySootClass(base_class);
      if(base_hclass == null){
        continue;
      }
      List<HierarchySootMethod> base_methods = base_hclass.getMethods(); 
      for(HierarchySootMethod method : base_methods){
        HierarchySootClass super_hclass = base_hclass;
        while(super_hclass.hasSuperClass()){
          super_hclass = getHierarchySootClass(super_hclass.getSuperClass());
          if(super_hclass == null){
            break;
          }
          if(super_hclass.declaresCovarientSubSignature(method.getCovarientSubSignature())){
            HierarchySootMethod super_hmethod = super_hclass.getMethodForCovarientSubSignature(method.getCovarientSubSignature());
            m_virtMap.put(method, super_hmethod);
            break;
          }
        }
      }          
    }

    Set<String> visited_sigs = new HashSet<String>();
    List<String> bfs_queue = new LinkedList<String>();
    bfs_queue.addAll(m_roots);

    while(bfs_queue.isEmpty() == false){
      String curr_class = bfs_queue.get(0);
      bfs_queue.remove(0);

      HierarchySootClass hclass = getHierarchySootClass(curr_class);
      if(hclass == null){
        continue;
      }

      List<HierarchySootMethod> methods = hclass.getMethods();
      for(HierarchySootMethod method : methods){
        String curr_sig = method.getSignature();
        if(visited_sigs.contains(curr_sig)){
          continue;
        }
        visited_sigs.add(curr_sig);

        List<String> path = new ArrayList<String>();
        path.add(curr_sig);
        m_virtualMethodSignatures.put(curr_sig, path);

        HierarchySootMethod trace_method = method;
        while(m_virtMap.containsKey(trace_method)){
          trace_method = m_virtMap.get(trace_method);
          String trace_sig = trace_method.getSignature();
          path.add(trace_sig);
          m_virtualMethodSignatures.put(trace_sig, path);
        }
      }

      if(hclass.hasSuperClass()){
        bfs_queue.add(hclass.getSuperClass());
      }
    }   
  }

  private void mapPut(Map<String, List<HierarchyGraph>> temp_graphs, String curr_class, 
    HierarchyGraph hgraph){

    List<HierarchyGraph> graphs;
    if(temp_graphs.containsKey(curr_class)){
      graphs = temp_graphs.get(curr_class);
    } else {
      graphs = new ArrayList<HierarchyGraph>();
      temp_graphs.put(curr_class, graphs);
    }
    graphs.add(hgraph);
  }

  public HierarchyGraph getHierarchyGraph(String signature){    
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);
    String class_name = util.getClassName();
    return m_hierarchyGraphs.get(class_name);
  }

  public HierarchyGraph getHierarchyGraph(SootClass soot_class){
    String class_name = soot_class.getName();
    return m_hierarchyGraphs.get(class_name);
  }

  public List<String> getVirtualMethods(String signature){
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);
    String class_name = util.getClassName();

    List<String> ret = new ArrayList<String>();
    if(util.getMethodName().equals("<init>") || util.getMethodName().equals("<clinit>")){
      ret.add(signature);
      return ret;
    }

    if(m_hierarchyGraphs.containsKey(class_name) == false){
      ret.add(signature);
      return ret;
    }

    Set<String> new_invokes = RootbeerClassLoader.v().getNewInvokes();  
    if(m_virtualMethodSignatures.containsKey(signature) == false){
      //todo: fix this
      //throw new RuntimeException("cannot find virtual signature: "+signature);
      ret.add(signature);
      return ret;
    }

    List<String> virt_sigs = m_virtualMethodSignatures.get(signature); 
    for(String virt_sig : virt_sigs){
      util.parse(virt_sig);
      String virt_class_name = util.getClassName();
      if(new_invokes.contains(virt_class_name)){
        ret.add(virt_sig);
      }
    }
  
    return ret;
  }

  @Override
  public String toString(){
    StringBuilder ret = new StringBuilder();    
    for(HierarchyGraph hgraph : m_hierarchyGraphs.values()){
      ret.append(hgraph.toString());
    }
    return ret.toString();
  }
}

