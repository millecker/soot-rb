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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.PrintWriter;
import java.io.StringReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.*;
import soot.Scene;
import soot.SootClass;
import soot.Type;

public class ClassRemapping {

  private Map<String, String> m_map;
  private Map<String, String> m_clonedMap;
  private List<String> m_runtimeClasses;
  private List<String> m_runtimeClassesJar;
  
  public ClassRemapping(){
    m_map = new HashMap<String, String>();
    m_clonedMap = new HashMap<String, String>();
    m_runtimeClasses = new ArrayList<String>();
    m_runtimeClassesJar = new ArrayList<String>();
    put("java.util.concurrent.atomic.AtomicLong", "edu.syr.pcpratts.rootbeer.runtime.remap.GpuAtomicLong");
    put("java.util.Random", "edu.syr.pcpratts.rootbeer.runtime.remap.Random");
    put("edu.syr.pcpratts.rootbeer.testcases.rootbeertest.remaptest.CallsPrivateMethod", "edu.syr.pcpratts.rootbeer.runtime.remap.DoesntCallPrivateMethod");
    put("java.lang.Math", "edu.syr.pcpratts.rootbeer.runtime.remap.java.lang.Math");
  }

  private void put(String key, String value) {
    m_map.put(key, value);
    m_runtimeClasses.add(value);
    value = "/" + value.replace(".", "/") + ".class";
    m_runtimeClassesJar.add(value);
  }
  
  public void cloneClass(String class_name){
    if(m_clonedMap.containsKey(class_name)){
      return;
    } 
    String new_name = "edu.syr.pcpratts.rootbeer.runtime.remap."+class_name;
    m_clonedMap.put(class_name, new_name);
    
    SootClass soot_class = Scene.v().getSootClass(class_name);
    CloneClass cloner = new CloneClass();
    SootClass new_class = cloner.execute(soot_class, new_name);
    new_class.setApplicationClass();
    Scene.v().addGeneratedClass(new_class);
  }
  
  
  public List<String> getRuntimeClasses(){
    return m_runtimeClasses;
  }
  
  public List<String> getRuntimeClassesJar(){
    return m_runtimeClassesJar;
  }

  public boolean containsKey(String cls_name) {
    return m_map.containsKey(cls_name);
  }

  public String get(String cls_name) {
    return m_map.get(cls_name);
  }

  public String remap(String cls_name){
    if(m_map.containsKey(cls_name)){
      return m_map.get(cls_name);
    }
    return cls_name;
  }
  
  public boolean cloned(String cls) {
    return m_clonedMap.containsKey(cls);
  }

  public List<String> getCloned() {
    List<String> ret = new ArrayList<String>();
    ret.addAll(m_clonedMap.values());
    return ret;
  }

  private String mapFilename(){
    return "/edu/syr/pcpratts/rootbeer/runtime/remap/remap.txt";
  }
  
  private String getResource(String path) throws IOException {
    InputStream is = ClassRemapping.class.getResourceAsStream(path);
    StringBuilder ret = new StringBuilder();
    BufferedReader reader = new BufferedReader(new InputStreamReader(is));
    while(true){
      String line = reader.readLine();
      if(line == null)
        break;
      ret.append(line + "\n");
    }
    is.close();
    return ret.toString();
  }
  
  public void loadMap() {
    String contents = "";
    String filename = mapFilename();
    try {
      contents = getResource(filename);
    } catch(Exception ex){
      contents = readFile("src"+filename);
    }
    doLoadMap(contents);
  }
  
  public void saveMap(){    
    String filename = "src"+mapFilename();
    try {
      PrintWriter writer = new PrintWriter(filename);
      Iterator<String> iter = m_clonedMap.keySet().iterator();
      while(iter.hasNext()){
        String key = iter.next();
        String value = m_clonedMap.get(key);
        writer.println(key+" => "+value);
      }
      writer.flush();
      writer.close();
    } catch(Exception ex){
      ex.printStackTrace();
    }
    
  }

  private String readFile(String filename) {
    String ret = "";
    try {
      BufferedReader reader = new BufferedReader(new FileReader(filename));
      while(true){
        String line = reader.readLine();
        if(line == null){
          break;
        }
        ret += line+"\n";
      }
      return ret;
    } catch(Exception ex){
      ex.printStackTrace();
      return ret;
    }    
  }

  private void doLoadMap(String contents) {
    try {
      BufferedReader reader = new BufferedReader(new StringReader(contents));
      while(true){
        String line = reader.readLine();
        if(line == null){
          break;
        }
        String[] tokens = line.split("=>");
        if(tokens.length != 2){
          continue;
        }
        m_clonedMap.put(tokens[0].trim(), tokens[1].trim()); 
        put(tokens[0].trim(), tokens[1].trim()); 
      }      
    } catch(Exception ex){
      ex.printStackTrace();
    }
  }

  public List<String> getUsed() {
    loadMap();
    List<String> ret = new ArrayList<String>();
    ret.addAll(m_runtimeClasses);
    ret.addAll(m_clonedMap.values());
    return ret;
  }

  public Collection<String> getValues() {
    return m_map.values();
  }

  public List<Type> getErasedTypes() {
    List<Type> ret = new ArrayList<Type>();
    for(String cls : m_map.keySet()){
      SootClass soot_class = Scene.v().getSootClass(cls);
      ret.add(soot_class.getType());
    }
    return ret;
  }

  public List<Type> getAddedTypes() {
    List<Type> ret = new ArrayList<Type>();
    for(String cls : m_map.values()){
      SootClass soot_class = Scene.v().getSootClass(cls);
      ret.add(soot_class.getType());
    }
    return ret;
  }
}
