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

import java.util.*;
import soot.*;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;

public class DfsInfo {

  private Set<String> m_dfsMethods;
  private Set<String> m_reverseDfsMethods;
  private Set<Type> m_dfsTypes;
  private List<Type> m_orderedTypes;
  private List<RefType> m_orderedRefTypes;
  private List<Type> m_orderedRefLikeTypes;
  private Set<SootField> m_dfsFields;
  private Set<ArrayType> m_arrayTypes;
  private List<Type> m_builtInTypes;
  private List<NumberedType> m_numberedTypes;
  private Set<Type> m_instanceOfs;
  private List<String> m_reachableMethodSigs;
  private String m_rootMethod;
  private List<SootMethod> m_otherEntryPoints;
  private Set<String> m_modifiedClasses;
  private StringCallGraph m_stringCallGraph;
  private Map<String, Set<Type>> m_pointsTo;
  private Set<String> m_reachableFields;
  private Set<String> m_interfaceSignatures;
  private Set<String> m_interfaceClasses;
  private Set<String> m_newInvokes;
  private Set<SootClass> m_validHierarchyClasses;

  public DfsInfo(String method_signature) {
    m_dfsMethods = new LinkedHashSet<String>();
    m_reverseDfsMethods = new LinkedHashSet<String>();
    m_dfsTypes = new HashSet<Type>();
    m_dfsFields = new HashSet<SootField>();
    m_builtInTypes = new ArrayList<Type>();
    m_instanceOfs = new HashSet<Type>();
    m_reachableMethodSigs = new ArrayList<String>();
    m_rootMethod = method_signature;
    m_otherEntryPoints = new ArrayList<SootMethod>();
    m_pointsTo = new HashMap<String, Set<Type>>();
    m_interfaceSignatures = new HashSet<String>();
    m_interfaceClasses = new HashSet<String>();
    m_newInvokes = new HashSet<String>();
    m_stringCallGraph = new StringCallGraph();
    m_numberedTypes = new ArrayList<NumberedType>();
    addBuiltInTypes();
  }

  public StringCallGraph getStringCallGraph(){
    return m_stringCallGraph;
  }
  
  public void expandArrayTypes(){  
    m_arrayTypes = new HashSet<ArrayType>();
    for(Type type : m_dfsTypes){
      if(type instanceof ArrayType){
        ArrayType array_type = (ArrayType) type;
        m_arrayTypes.add(array_type);
      }
    }
    
    MultiDimensionalArrayTypeCreator creator = new MultiDimensionalArrayTypeCreator();
    Set<ArrayType> added = creator.create(m_arrayTypes);
    m_dfsTypes.addAll(added);
    m_arrayTypes.addAll(added);
  }
  
  private void printSet(String name, Set curr_set) {
    System.out.println(name);
    for(Object curr : curr_set){
      System.out.println("  "+curr.toString());
    }
  }

  public List<String> getForwardReachables() {
    List<String> ret = new ArrayList<String>();
    ret.addAll(m_dfsMethods);
    return ret;
  }

  public void addMethod(String signature) {
    if(m_dfsMethods.contains(signature) == false){
      m_dfsMethods.add(signature);
    }
    addReachableMethodSig(signature);
  }

  public boolean containsMethod(String signature) {
    return m_dfsMethods.contains(signature);
  }

  public boolean containsType(Type name) {
    return m_dfsTypes.contains(name);
  }

  public Set<Type> getDfsTypes(){
    return m_dfsTypes;
  }

  public boolean reachesJavaLangClass(){
    for(Type type : m_dfsTypes){
      if(type instanceof RefType){
        RefType ref_type = (RefType) type;
        String class_name = ref_type.getClassName();
        if(class_name.equals("java.lang.Class")){
          return true;
        }
      }
    }
    return false;
  }

  public void addType(Type name) {
    if(m_dfsTypes.contains(name) == false){
      m_dfsTypes.add(name);
    }
  }

  private SootClass getSootClassIfPossible(Type type){
    if(type instanceof ArrayType){
      ArrayType array_type = (ArrayType) type;
      return getSootClassIfPossible(array_type.baseType);
    } else if(type instanceof RefType){
      RefType ref_type = (RefType) type;
      return ref_type.getSootClass();
    } else {
      return null;
    }
  }
  
  public void addField(SootField field){
    if(m_dfsFields.contains(field) == false){
      m_dfsFields.add(field);
    }
  }

  public List<Type> getOrderedTypes() {
    return m_orderedTypes;
  }

  public List<RefType> getOrderedRefTypes() {
    return m_orderedRefTypes;
  }

  public Set<String> getMethods() {
    return m_dfsMethods;
  }

  public Set<String> getReverseMethods(){
    return m_reverseDfsMethods;
  }

  public void addReverseDfsMethod(String sig){
    m_reverseDfsMethods.add(sig);
  }

  public Set<SootField> getFields() {
    return m_dfsFields;
  }

  public Set<ArrayType> getArrayTypes() {
    return m_arrayTypes;
  }

  private void addBuiltInTypes() {
    String prefix = Options.v().rbcl_remap_prefix();
    if(Options.v().rbcl_remap_all() == false){
      prefix = "";
    }
    addRefType("java.lang.Object");
    addRefType(prefix+"java.lang.Class");
    addRefType(prefix+"java.lang.System");
    addRefType("java.lang.String");
    addRefType(prefix+"java.lang.AbstractStringBuilder");
    addRefType(prefix+"java.lang.StringBuilder");
    addRefType(prefix+"java.lang.StackTraceElement");
    addRefType(prefix+"java.lang.Throwable");
    addRefType(prefix+"java.lang.Exception");
    addRefType(prefix+"java.lang.RuntimeException");
    addRefType(prefix+"java.lang.NullPointerException");
    addRefType(prefix+"java.lang.Error");
    addRefType(prefix+"java.lang.VirtualMachineError");
    addRefType(prefix+"java.lang.OutOfMemoryError");

    m_builtInTypes.add(ByteType.v());
    m_builtInTypes.add(CharType.v());
    m_builtInTypes.add(ShortType.v());
    m_builtInTypes.add(IntType.v());
    m_builtInTypes.add(LongType.v());
    m_builtInTypes.add(FloatType.v());
    m_builtInTypes.add(DoubleType.v());
    m_builtInTypes.add(BooleanType.v());
    m_builtInTypes.add(VoidType.v());
    m_builtInTypes.add(NullType.v());
    
    ArrayType char_arr = ArrayType.v(CharType.v(), 1);
    m_builtInTypes.add(char_arr);
  }

  private void addRefType(String class_name) {
    SootResolver.v().resolveClass(class_name, SootClass.HIERARCHY);
    SootClass soot_class = Scene.v().getSootClass(class_name);
    m_builtInTypes.add(soot_class.getType());
  }

  public List<Type> getBuiltInTypes(){
    return m_builtInTypes;
  }

  public List<Type> getOrderedRefLikeTypes() {
    return m_orderedRefLikeTypes;
  }

  public Set<Type> getInstanceOfs() {
    return m_instanceOfs;
  }

  public void addInstanceOf(Type type) {
    if(m_instanceOfs.contains(type) == false){
      m_instanceOfs.add(type);
    }
  }
  
  public List<String> getReachableMethodSigs(){
    return m_reachableMethodSigs;
  }
  
  public void addReachableMethodSig(String signature){
    if(m_reachableMethodSigs.contains(signature) == false){
      m_reachableMethodSigs.add(signature);
    }
  }
  
  public Set<String> getAllMethods() {
    Set<String> ret = new HashSet<String>();
    ret.addAll(m_dfsMethods);
    ret.addAll(m_reachableMethodSigs);
    return ret;
  }

  public SootMethod getRootMethod() {
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(m_rootMethod);
    return util.getSootMethod();
  }

  public Set<String> getInterfaceSignatures(){
    return m_interfaceSignatures;
  }

  public String getRootMethodSignature() {
    return m_rootMethod;
  }

  public List<SootMethod> getOtherEntryPoints(){
    return m_otherEntryPoints;
  }

  public void setModifiedClasses(Set<String> modified_classes) {
    m_modifiedClasses = modified_classes;
  }
  
  public Set<String> getModifiedClasses(){
    return m_modifiedClasses;
  }

  public void finalizeTypes(){
    //read in NumberedTypes
    ClassHierarchy class_hierarchy = RootbeerClassLoader.v().getClassHierarchy();
    List<NumberedType> numbered_types = class_hierarchy.getNumberedTypes();
    for(NumberedType ntype : numbered_types){
      Type type = ntype.getType();
      if(m_dfsTypes.contains(type) || m_arrayTypes.contains(type)){
        m_numberedTypes.add(ntype);
        m_orderedTypes.add(type);
        if(type instanceof RefType){
          RefType ref_type = (RefType) type;
          m_orderedRefTypes.add(ref_type);
        }
        if(type instanceof RefLikeType){
          m_orderedRefLikeTypes.add(type);
        }
      }
    }
  }

  public List<NumberedType> getNumberedTypes(){
    return m_numberedTypes;
  }

  /**
   *  Get List<NumberedTypes> that are super types of soot_class
   */
  public List<NumberedType> getNumberedHierarchyDown(SootClass soot_class){
    ClassHierarchy class_hierarchy = RootbeerClassLoader.v().getClassHierarchy();
    HierarchyGraph hgraph = class_hierarchy.getHierarchyGraph(soot_class);
    List<String> parents = hgraph.getParents(soot_class.getName());
    System.out.println("DfsInfo.getNumberedHierarchyDown: "+soot_class.getName());
    for(String parent : parents){
      System.out.println("  "+parent);
    }
    System.exit(0);
    return null;
  }

}
