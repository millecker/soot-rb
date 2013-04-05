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
import soot.rbclassload.HierarchySootMethod;
import soot.rbclassload.HierarchyInstruction;
import soot.rbclassload.ClassPoolConstantReader;

public class HierarchySootMethodFactory {

  private cp_info[] m_constantPool;
  private ClassPoolConstantReader m_constantReader;

  public HierarchySootMethodFactory(){
    m_constantReader = new ClassPoolConstantReader();
  }

  public HierarchySootMethod create(method_info methodInfo, ClassFile classFile){
    m_constantPool = classFile.constant_pool;

    CONSTANT_Utf8_info utf8_name = (CONSTANT_Utf8_info) class_file.constant_pool[mi.name_index];
    name = utf8_name.convert();

    String type_descr = cp_info.getTypeDescr(class_file.constant_pool, mi.descriptor_index);
    String[] tokens = type_descr.split("\\)");
    String return_desc = tokens[1];
    String parameter_desc = tokens[0].substring(1);

    returnType = ClassFile.parseDesc(return_desc, ",");
    String parsedParameterTypes = ClassFile.parseDesc(parameter_desc, ",");
    String[] parameters = parsedParameterTypes.split(",");
    for(String param : parameters){
      parameterTypes.add(param);
    }

    attribute_info exceptions_attr = findExceptionsAttribute(mi);
    if(exceptions_attr != null){
      Exception_attribute ex_attribute = (Exception_attribute) exceptions_attr;
      GetClassConstant constant_reader = new GetClassConstant();
      for(int table_index : ex_attribute.exception_index_table){
        exceptionTypes.add(constant_reader.get(table_index, m_classFile));
      }      
    }

    List<HierarchyInstruction> instructions = new ArrayList<HierarchyInstruction>();
    Instruction inst = mi.instructions;
    while(inst != null){
      HierarchyInstruction hinst = parseInstruction(inst);      
      instructions.add(hinst);
      inst = inst.next;
    }

    HierarchySootMethod ret = new HierarchySootMethod(name, returnType,
      parameterTypes, exceptionTypes, instructions);
    return ret;
  }

  private HierarchyInstruction parseInstruction(Instruction inst){
    String name = inst.name;
    List<String> arguments = new ArrayList<String>();
    if(inst instanceof Instruction_noargs){
      //ignore
    } else if(inst instanceof Instruction_byte){
      Instruction_byte inst_byte = (Instruction_byte) inst;
      String arg0 = Byte.parseByte(inst_byte.arg_b).toString();
      arguments.add(arg0);
    } else if(inst instanceof Instruction_bytevar){
      Instruction_bytevar inst_bytevar = (Instruction_bytevar) inst;
      String arg0 = Integer.parseInt(inst_bytevar.arg_b).toString();
      argments.add(arg0);
    } else if(inst instanceof Instruction_byteindex){
      Instruction_byteindex inst_byteindex = (Instruction_byteindex) inst;  
      String arg0 = m_constantReader.get(inst_byteindex.arg_b, m_constantPool);
      arguments.add(arg0);
    } else if(inst instanceof Instruction_int){
      Instruction_int inst_int = (Instruction_int) inst;
      String arg0 = Integer.parseInt(inst_int.arg_i).toString();
      arguments.add(arg0);
    } else if(inst instanceof Instruction_intvar){
      Instruction_intvar inst_intvar = (Instruction_intvar) inst;
      String arg0 = Integer.parseInt(inst_intvar.arg_i).toString();
      arguments.add(arg0);
    } else if(inst instanceof Instruction_intindex){
      Instruction_intindex inst_intindex = (Instruction_intindex) inst;
      String arg0 = m_constantReader.get(inst_intindex.arg_i, m_constantPool);
      arguments.add(arg0);
    } else if(inst instanceof Instruction_intbranch){
      Instruction_intbranch inst_intbranch = (Instruction_intbranch) inst;
      String arg0 = Integer.parseInt(inst_intbranch.arg_i).toString();
      arguments.add(arg0);
    } else if(inst instanceof Instruction_longbranch){
      Instruction_longbranch inst_longbranch = (Instruction_longbranch) inst;
      String arg0 = Integer.parseInt(inst_longbranch.arg_i).toString();
      arguments.add(arg0);
    } else {
      throw new RuntimeException("unknown instruction type: "+inst.toString());
    } 
    HierarchyInstruction ret = new HierarchyInstruction(name, arguments);
    return 
  }
  
  private attribute_info findExceptionsAttribute(method_info mi){
    if(m_classFile.attributes == null){
      return null;
    }
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

