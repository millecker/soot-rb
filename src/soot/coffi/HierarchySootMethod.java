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

public class HierarchySootMethod {

  private String m_name;
  private String m_returnType;
  private List<String> m_parameterTypes;
  private List<String> m_exceptionTypes;

  private ClassFile m_classFile;

  public HierarchySootMethod(){
    m_parameterTypes = new ArrayList<String>();
    m_exceptionTypes = new ArrayList<String>();
  }

  public void read(method_info mi, ClassFile class_file){
    m_classFile = class_file;    

    CONSTANT_Utf8_info utf8_name = (CONSTANT_Utf8_info) class_file.constant_pool[mi.name_index];
    m_name = utf8_name.convert();

    String type_descr = cp_info.getTypeDescr(class_file.constant_pool, mi.descriptor_index);
    String[] tokens = type_descr.split("\\)");
    String return_desc = tokens[1];
    String parameter_desc = tokens[0].substring(1);

    m_returnType = ClassFile.parseDesc(return_desc, ",");
    String parameter_types = ClassFile.parseDesc(parameter_desc, ",");
    String[] parameters = parameter_types.split(",");
    for(String param : parameters){
      m_parameterTypes.add(param);
    }

    attribute_info exceptions_attr = findExceptionsAttribute(mi);
    if(exceptions_attr != null){
      Exception_attribute ex_attribute = (Exception_attribute) exceptions_attr;
      GetClassConstant constant_reader = new GetClassConstant();
      for(int table_index : ex_attribute.exception_index_table){
        m_exceptionTypes.add(constant_reader.get(table_index, m_classFile));
      }      
    }
  }
  
  private attribute_info findExceptionsAttribute(method_info mi){
    for(attribute_info attribute : m_classFile.attributes){
      int name_index = attribute.attribute_name;
      CONSTANT_Utf8_info utf8_name = (CONSTANT_Utf8_info) m_classFile.constant_pool[name_index];
      String attribute_name = utf8_name.convert();
      if(attribute_name.equals(attribute_info.Exceptions)){
        return attribute;
      }
    }
    return null;
  }

  public String getName(){
    return m_name;
  }

  public String getReturnType(){
    return m_returnType;
  }

  public List<String> getParameterTypes(){
    return m_parameterTypes;
  }

  public List<String> getExceptionTypes(){
    return m_exceptionTypes;
  }
}
