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

package soot.coffi;

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

  private ClassFile m_classFile;
/*
  ClassFile fields:
    public int constant_pool_count;
    public cp_info constant_pool[];
    public int access_flags;
    public int this_class;
    public int super_class;
    public int interfaces_count;
    public int interfaces[];
    public int fields_count;
    public field_info fields[];
    public int methods_count;
    public method_info methods[];
    public int attributes_count;
    public attribute_info attributes[];
*/

  public HierarchySootClass(String name){
    m_className = name;
    m_interfaceNames = new ArrayList<String>();
    m_methods = new ArrayList<HierarchySootMethod>();
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

  public boolean loadClassFile(String filename, InputStream is){
    m_classFile = new ClassFile(filename);
    DataInputStream data_stream = new DataInputStream(is);
    boolean loaded = m_classFile.readClass(data_stream);
    if(loaded == false){
      return false;
    }

    GetClassConstant constant_reader = new GetClassConstant();
    if(m_classFile.super_class == 0){
      m_hasSuperClass = false;
    } else {
      m_hasSuperClass = true;
      m_superClassName = constant_reader.get(m_classFile.super_class, m_classFile);
    }

    for(int i = 0; i < m_classFile.interfaces_count; ++i){
      String name = constant_reader.get(m_classFile.interfaces[i], m_classFile);
      m_interfaceNames.add(name);
    }
    
    for(int i = 0; i < m_classFile.methods_count; ++i){
      HierarchySootMethod method = new HierarchySootMethod();
      method.read(m_classFile.methods[i], m_classFile);
      m_methods.add(method);
    }
    m_classFile = null;
    return true;
  }
}
