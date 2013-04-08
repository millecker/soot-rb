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
  private Set<String> m_methodRefs;
  private Set<String> m_fieldRefs;
  private MethodSignatureUtil m_methodUtil;
  private FieldSignatureUtil m_fieldUtil;
  private StringToType m_stringToType;

  public HierarchyValueSwitch(){
    m_classes = new HashSet<String>();
    m_methodRefs = new HashSet<String>();
    m_fieldRefs = new HashSet<String>();
    m_methodUtil = new MethodSignatureUtil();
    m_fieldUtil = new FieldSignatureUtil();
    m_stringToType = new StringToType();
  }

  public Set<String> getClasses(){
    return m_classes;
  }

  public Set<String> getMethodRefs(){
    return m_methodRefs;
  }

  public Set<String> getFieldRefs(){
    return m_fieldRefs;
  }

  public void run(String signature){
    ClassHierarchy class_hierarchy = RootbeerClassLoader.v().getClassHierarchy();
    HierarchySootMethod method = class_hierarchy.getHierarchySootMethod(signature);
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
    List<Operand> operands = inst.getOperands();
    for(Operand operand : operands){
      String value = operand.getValue();
      String type = operand.getType();

      if(type.equals("class_ref")){
        m_classes.add(value);
      } else if(type.equals("method_ref")){
        System.out.println("method_ref: "+value);
        m_methodRefs.add(value);
        m_methodUtil.parse(value);
        m_classes.add(m_methodUtil.getClassName());
        addRefType(m_methodUtil.getReturnType());
        for(String param : m_methodUtil.getParameterTypes()){
          addRefType(param);
        }
      } else if(type.equals("field_ref")){
        m_fieldRefs.add(value);
        m_fieldUtil.parse(value);
        m_classes.add(m_fieldUtil.getDeclaringClass());
        addRefType(m_fieldUtil.getType());
      } 
    }
  }

  private void addRefType(String type_string){
    if(m_stringToType.isRefType(type_string)){
      m_classes.add(type_string);
    }
  }
}
