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
import soot.coffi.ConstantPoolReader;
import soot.rbclassload.HierarchySootClass;
import soot.rbclassload.HierarchySootMethod;

public class HierarchySootClassFactory {

  private ConstantPoolReader m_constantReader;
  private HierarchySootMethodFactory m_methodFactory;

  public HierarchySootClassFactory(){
    m_constantReader = new ConstantPoolReader();
    m_methodFactory = new HierarchySootMethodFactory();
  }

  public HierarchySootClass create(String filename, InputStream is){
    ClassFile classFile = new ClassFile(filename);

    DataInputStream dataStream = new DataInputStream(is);
    boolean loaded = classFile.readClass(dataStream);
    if(loaded == false){
      return null;
    }
    cp_info[] constantPool = classFile.constant_pool;

    boolean hasSuperClass;
    String className;
    String superClassName;

    className = m_constantReader.get(classFile.this_class, constantPool);

    if(classFile.super_class == 0){
      hasSuperClass = false;
      superClassName = "";
    } else {
      hasSuperClass = true;
      superClassName = m_constantReader.get(classFile.super_class, constantPool);
    }

    List<String> interfaces = new ArrayList<String>();
    for(int i = 0; i < classFile.interfaces_count; ++i){
      String name = m_constantReader.get(classFile.interfaces[i], constantPool);
      interfaces.add(name);
    }
    
    int modifiers = classFile.access_flags & ~0x0020;

    HierarchySootClass ret = new HierarchySootClass(className, hasSuperClass,
      superClassName, interfaces, modifiers, classFile);

    return ret;
  }
}
