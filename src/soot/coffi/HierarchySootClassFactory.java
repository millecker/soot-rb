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

public class HierarchySootClassFactory {

  public HierarchySootClass create(String filename, InputStream is){
    m_classFile = new ClassFile(filename);
    m_constantPool = m_classFile.constant_pool;

    DataInputStream data_stream = new DataInputStream(is);
    boolean loaded = m_classFile.readClass(data_stream);
    if(loaded == false){
      return null;
    }

    boolean hasSuperClass;
    String superClassName;

    GetClassConstant constant_reader = new GetClassConstant();
    if(m_classFile.super_class == 0){
      hasSuperClass = false;
    } else {
      hasSuperClass = true;
      superClassName = constant_reader.get(m_classFile.super_class, m_classFile);
    }

    List<String> interfaces = new ArrayList<String>();
    for(int i = 0; i < m_classFile.interfaces_count; ++i){
      String name = constant_reader.get(m_classFile.interfaces[i], m_classFile);
      interfaces.add(name);
    }
    
    HierarchySootMethodFactory methodFactory = new HierarchySootMethodFactory();
    List<HierarchySootMethod> methods = new ArrayList<HierarchySootMethod>();
    for(int i = 0; i < m_classFile.methods_count; ++i){
      HierarchySootMethod method = methodFactory.create(m_classFile.methods[i], m_classFile);
      method.setHierarchySootClass(this);
      methods.add(method);
    }
    m_classFile = null;

    HierarchySootClass ret = new HierarchySootClass(className, hasSuperClass,
      superClassName, interfaces, methods);
    return ret;;
  }
}
