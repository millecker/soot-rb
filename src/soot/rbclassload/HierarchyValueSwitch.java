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
import java.util.Set;
import java.util.HashSet;

public class HierarchyValueSwitch {

  private Set<String> m_classes;
  private Set<String> m_types;
  private Set<String> m_arrayTypes;
  private Set<String> m_methodRefs;
  private Set<String> m_fieldRefs;
  private Set<String> m_instanceofs;
  private Set<String> m_newInvokes;
  private MethodSignatureUtil m_methodUtil;
  private FieldSignatureUtil m_fieldUtil;
  private StringToType m_stringToType;

  public HierarchyValueSwitch(){
    m_classes = new HashSet<String>();
    m_types = new HashSet<String>();
    m_arrayTypes = new HashSet<String>();
    m_methodRefs = new HashSet<String>();
    m_fieldRefs = new HashSet<String>();
    m_instanceofs = new HashSet<String>();
    m_newInvokes = new HashSet<String>();
    m_methodUtil = new MethodSignatureUtil();
    m_fieldUtil = new FieldSignatureUtil();
    m_stringToType = new StringToType();
  }

  public Set<String> getClasses(){
    return m_classes;
  }

  public Set<String> getTypes(){
    return m_types;
  }

  public Set<String> getArrayTypes(){
    return m_arrayTypes;
  }

  public Set<String> getMethodRefs(){
    return m_methodRefs;
  }

  public Set<String> getFieldRefs(){
    return m_fieldRefs;
  }

  public Set<String> getInstanceOfs(){
    return m_instanceofs;
  }

  public Set<String> getNewInvokes(){
    return m_newInvokes;
  }

  public void run(String signature){
    ClassHierarchy class_hierarchy = RootbeerClassLoader.v().getClassHierarchy();
    HierarchySootMethod method = class_hierarchy.getHierarchySootMethod(signature);
    if(method == null){
      return;
    }

    HierarchySootClass hclass = method.getHierarchySootClass();

    if(method.isConcrete() == false){
      return;
    }

    addHierarchy(hclass);
    addSignature(method);
    
    List<HierarchyInstruction> instructions = method.getInstructions();
    for(HierarchyInstruction inst : instructions){
      addInstruction(inst);
    }
  }

  private void addHierarchy(HierarchySootClass hclass){
    m_classes.add(hclass.getName());
    if(hclass.hasSuperClass()){
      m_classes.add(hclass.getSuperClass());
    }
    for(String iface : hclass.getInterfaces()){
      m_classes.add(iface);
    }
  }

  private void addSignature(HierarchySootMethod method){
    m_classes.add(method.getReturnType());
    for(String param : method.getParameterTypes()){
      m_classes.add(param);
    }
    for(String except : method.getExceptionTypes()){
      m_classes.add(except);
    }
  }
  
  private void addInstruction(HierarchyInstruction inst){
    addInstructionName(inst);
    addInstructionOperands(inst);
  }

  private void addInstructionName(HierarchyInstruction inst){
    String name = inst.getName();
    if(name.equals("anewarray")){
      addNewInvoke(inst);
    } else if(name.equals("instanceof")){
      addInstanceOf(inst);
    } else if(name.equals("multianewarray")){
      addNewInvoke(inst);
    } else if(name.equals("newarray")){
      addNewInvoke(inst);
    } else if(name.equals("new")){
      addNewInvoke(inst);
    }
  }

  private void addInstructionOperands(HierarchyInstruction inst){
    List<Operand> operands = inst.getOperands();
    for(Operand operand : operands){
      String value = operand.getValue();
      String type = operand.getType();

      if(type.equals("class_ref")){
        m_classes.add(value);
      } else if(type.equals("method_ref")){
        m_methodRefs.add(value);
        m_methodUtil.parse(value);
        m_classes.add(m_methodUtil.getClassName());
        addType(m_methodUtil.getReturnType());
        for(String param : m_methodUtil.getParameterTypes()){
          addType(param);
        }
      } else if(type.equals("field_ref")){
        m_fieldRefs.add(value);
        m_fieldUtil.parse(value);
        m_classes.add(m_fieldUtil.getDeclaringClass());
        addType(m_fieldUtil.getType());
      } 
    }
  }

  private void addType(String type_string){
    if(m_stringToType.isRefType(type_string)){
      m_classes.add(type_string);
    }
    if(m_stringToType.isArrayType(type_string)){
      m_arrayTypes.add(type_string);
    }
    m_types.add(type_string);
  }

  private void addNewInvoke(HierarchyInstruction inst){
    List<Operand> operands = inst.getOperands();
    for(Operand operand : operands){
      String value = operand.getValue();
      String type = operand.getType();

      if(type.equals("class_ref")){
        m_newInvokes.add(value);
      }
    }
  }

  private void addInstanceOf(HierarchyInstruction inst){
    List<Operand> operands = inst.getOperands();
    for(Operand operand : operands){
      String value = operand.getValue();
      String type = operand.getType();

      if(type.equals("class_ref")){
        m_instanceofs.add(value);
      }
    }
  }
}
