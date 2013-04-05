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

import java.util.List;
import java.util.ArrayList;
import java.io.InputStream;
import java.io.DataInputStream;
import java.io.IOException;

public class HierarchySootClass {

  private String m_className;
  private boolean m_hasSuperClass;
  private String m_superClassName;
  private List<String> m_interfaceNames;
  private List<HierarchySootMethod> m_methods;  

  public HierarchySootClass(String class_name, boolean has_super_class, 
    String super_class_name, List<String> interfaces, 
    List<HierarchySootMethod> methods){

    m_className = class_name;
    m_hasSuperClass = has_super_class;
    m_superClassName = super_class_name;
    m_interfaceNames = interfaces;
    m_methods = methods;
  }

  public String getName(){
    return m_className;
  }

  public boolean hasSuperClass(){
    return m_hasSuperClass;
  }

  public String getSuperClass(){
    return m_superClassName;
  }

  public List<String> getInterfaces(){
    return m_interfaceNames;
  }

  public List<HierarchySootMethod> getMethods(){
    return m_methods;
  }

  public HierarchySootMethod findMethodByName(String name){
    for(HierarchySootMethod method : m_methods){
      if(method.getName().equals(name)){
        return method;
      }
    }
    return null;
  }

  public HierarchySootMethod findMethodBySubSignature(String sub_sig){
    for(HierarchySootMethod method : m_methods){
      if(method.getSubSignature().equals(sub_sig)){
        return method;
      }
    }
    return null;
  }
}
