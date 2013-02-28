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
  private CallGraph m_callGraph;
  private Map<String, List<Type>> m_parentsToChildren;
  private Map<String, List<NumberedType>> m_childrenToParents;
  private Map<String, List<NumberedType>> m_hierarchyDown;
  private Map<String, NumberedType> m_numberedTypeMap;
  private List<NumberedType> m_numberedTypes;
  private List<Type> m_orderedTypes;
  private List<RefType> m_orderedRefTypes;
  private List<Type> m_orderedRefLikeTypes;
  private Set<SootField> m_dfsFields;
  private Set<ArrayType> m_arrayTypes;
  private List<Type> m_builtInTypes;
  private Map<SootClass, Integer> m_classToNumber;
  private Set<Type> m_instanceOfs;
  private List<String> m_reachableMethodSigs;
  private SootMethod m_rootMethod;
  private List<SootMethod> m_otherEntryPoints;
  private Set<String> m_modifiedClasses;
  private StringCallGraph m_stringCallGraph;

  public DfsInfo(SootMethod soot_method) {
    m_dfsMethods = new LinkedHashSet<String>();
    m_reverseDfsMethods = new LinkedHashSet<String>();
    m_dfsTypes = new HashSet<Type>();
    m_dfsFields = new HashSet<SootField>();
    m_callGraph = new CallGraph();
    m_builtInTypes = new ArrayList<Type>();
    m_instanceOfs = new HashSet<Type>();
    m_reachableMethodSigs = new ArrayList<String>();
    m_parentsToChildren = new HashMap<String, List<Type>>();
    m_rootMethod = soot_method;
    m_otherEntryPoints = new ArrayList<SootMethod>();
    addBuiltInTypes();
  }

  public void setStringCallGraph(StringCallGraph cg){
    m_stringCallGraph = cg;
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
    SootClass obj_class = Scene.v().getSootClass("java.lang.Object");
    for(Type added_type : m_arrayTypes){
      addSuperClass(added_type, obj_class.getType());
    }
  }
  
  public void orderTypes(){
    m_numberedTypeMap = new HashMap<String, NumberedType>();
    m_classToNumber = new HashMap<SootClass, Integer>();
    
    List<NumberedType> numbered_types = new ArrayList<NumberedType>();
    int number = 1;
    List<Type> queue = new LinkedList<Type>();
    Set<Type> visited = new HashSet<Type>();
    queue.addAll(m_builtInTypes);
    while(queue.isEmpty() == false){
      Type curr = queue.get(0);
      queue.remove(0);
      
      if(visited.contains(curr)){
        continue;
      }
      visited.add(curr);
      
      NumberedType numbered_type = new NumberedType(curr, number);
      numbered_types.add(numbered_type);
      m_numberedTypeMap.put(curr.toString(), numbered_type);
      if(curr instanceof RefType){
        RefType ref_type = (RefType) curr;
        SootClass curr_class = ref_type.getSootClass();
        m_classToNumber.put(curr_class, number);
      }
      
      number++;
      
      if(m_parentsToChildren.containsKey(curr.toString()) == false){
        continue;
      }
      
      List<Type> children = m_parentsToChildren.get(curr.toString());
      queue.addAll(children);
    }
    
    m_numberedTypes = new ArrayList<NumberedType>();
    m_orderedTypes = new ArrayList<Type>();
    m_orderedRefTypes = new ArrayList<RefType>();
    m_orderedRefLikeTypes = new ArrayList<Type>();
    for(int i = numbered_types.size() - 1; i >= 0; --i){
      NumberedType curr2 = numbered_types.get(i);
      m_numberedTypes.add(curr2);
      m_orderedTypes.add(curr2.getType());
      
      Type type = curr2.getType();
      if(type instanceof RefType){
        RefType ref_type = (RefType) type;
        m_orderedRefTypes.add(ref_type);
      } 
      if(type instanceof RefLikeType){
        m_orderedRefLikeTypes.add(type);
      }
    }
  }
  
  private NumberedType getNumberedType(String str){
    if(m_numberedTypeMap.containsKey(str)){
      return m_numberedTypeMap.get(str);
    } else {
      System.out.println("cannot find numbered type: "+str);
      Iterator<String> iter = m_numberedTypeMap.keySet().iterator();
      while(iter.hasNext()){
        System.out.println("  "+iter.next());
      }      
      System.exit(0);
      return null;
    }
  }

  public void createClassHierarchy(){
    m_childrenToParents = new HashMap<String, List<NumberedType>>();
    Set<Type> to_process = new HashSet<Type>();
    to_process.addAll(m_dfsTypes);
    to_process.addAll(m_builtInTypes);
    for(Type type : to_process){
      List<NumberedType> parents = new ArrayList<NumberedType>();
      NumberedType curr_type = getNumberedType(type.toString());
      parents.add(curr_type);
      if(type instanceof RefType){
        RefType ref_type = (RefType) type;
        SootClass curr_class = ref_type.getSootClass();
        while(curr_class.hasSuperclass()){
          curr_class = curr_class.getSuperclass();
          parents.add(getNumberedType(curr_class.getType().toString()));
        }
      } else if(type instanceof ArrayType){
        SootClass obj_cls = Scene.v().getSootClass("java.lang.Object");
        parents.add(getNumberedType(obj_cls.getType().toString()));
      } else {
        continue;
      }
      m_childrenToParents.put(type.toString(), parents);
    }
    
    m_hierarchyDown = new HashMap<String, List<NumberedType>>();
    SootClass obj_cls = Scene.v().getSootClass("java.lang.Object");
    Type root = obj_cls.getType();
    List<Type> stack = new ArrayList<Type>();
    stack.add(root);
    hierarchyDfs(root, stack);
  }
  
  private void hierarchyDfs(Type curr, List<Type> stack){ 
    List<Type> children = m_parentsToChildren.get(curr.toString());
    if(children == null){
      children = new ArrayList<Type>(); 
    }
    for(Type child : children){
      stack.add(child);
      hierarchyDfs(child, stack);
      stack.remove(stack.size()-1);
    }
    for(int i = 0; i < stack.size(); ++i){
      Type stack_value = stack.get(i);
      List<NumberedType> curr_parents = null;
      if(m_hierarchyDown.containsKey(stack_value.toString())){
        curr_parents = m_hierarchyDown.get(stack_value.toString());
      } else {
        curr_parents = new ArrayList<NumberedType>();
        m_hierarchyDown.put(stack_value.toString(), curr_parents);
      }
      for(int j = i; j < stack.size(); ++j){
        Type child = stack.get(j); 
        NumberedType ntype = m_numberedTypeMap.get(child.toString());
        if(curr_parents.contains(ntype) == false){
          curr_parents.add(ntype);
        }
      }
    }    
  }
  
  public List<NumberedType> getNumberedTypes(){
    return m_numberedTypes;
  }

  public void print() {
    printSet("methods: ", getMethods());
    printSet("fields: ", getFields());
    printSet("array_types: ", getArrayTypes());
    printSet("instance_ofs: ", getInstanceOfs());
    
    System.out.println("parentsToChildren: ");
    for(String parent : m_parentsToChildren.keySet()){
      List<Type> children = m_parentsToChildren.get(parent);
      System.out.println("  "+parent);
      for(Type child : children){
        System.out.println("    "+child);
      }
    }
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
    if(name instanceof ArrayType){
      SootClass object_class = Scene.v().getSootClass("java.lang.Object");
      addSuperClass(name, object_class.getType());
      return;
    }
    SootClass type_class = getSootClassIfPossible(name);
    if(type_class == null){
      return;
    }
    if(type_class.hasSuperclass() == false){
      return;
    }
    SootClass parent_class = type_class.getSuperclass();
    addSuperClass(name, parent_class.getType());
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

  public void addSuperClass(Type curr, Type superclass) {
    if(m_parentsToChildren.containsKey(superclass.toString())){
      List<Type> children = m_parentsToChildren.get(superclass.toString());
      if(children.contains(curr) == false){
        children.add(curr);
      }
    } else {
      List<Type> children = new ArrayList<Type>();
      children.add(curr);
      m_parentsToChildren.put(superclass.toString(), children);
    }
    if(superclass instanceof RefType){
      RefType super_ref = (RefType) superclass;
      SootClass super_soot_class = super_ref.getSootClass();
      if(super_soot_class.hasSuperclass()){
        SootClass new_super = super_soot_class.getSuperclass();
        addSuperClass(superclass, new_super.getType());
      }
    } else if(superclass instanceof ArrayType){
      RefType obj_type = RefType.v("java.lang.Object");
      addSuperClass(superclass, obj_type);
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

  public List<Type> getHierarchy(SootClass input_class) {
    List<NumberedType> nret = m_childrenToParents.get(input_class.getType().toString());
    List<Type> ret = new ArrayList<Type>();
    for(NumberedType ntype : nret){
      ret.add(ntype.getType());
    }
    nret = m_hierarchyDown.get(input_class.getType().toString());
    for(NumberedType ntype : nret){
      ret.add(ntype.getType());
    }
    return ret;
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

  public List<NumberedType> getNumberedHierarchyUp(SootClass sootClass) {
    return m_childrenToParents.get(sootClass.getType().toString());
  }

  public int getClassNumber(SootClass soot_class) {
    if(m_classToNumber.containsKey(soot_class)){
      return m_classToNumber.get(soot_class);
    } else {
      System.out.println("cannot find number for soot_class: "+soot_class.getName());
      Iterator<SootClass> iter = m_classToNumber.keySet().iterator();
      while(iter.hasNext()){
        SootClass key = iter.next();
        int value = m_classToNumber.get(key);
        System.out.println("  ["+key.getName()+", "+value+"]");
      }
      try {
        throw new RuntimeException("quit");
      } catch(Exception ex){
        ex.printStackTrace();
        System.exit(0);
      }
      return 0;
    }
  }
  
  public int getClassNumber(Type type) {
    if(m_numberedTypeMap.containsKey(type.toString())){
      return (int) m_numberedTypeMap.get(type.toString()).getNumber();
    } else {
      System.out.println("cannot find class number for type: "+type.toString());
      Iterator<String> iter = m_numberedTypeMap.keySet().iterator();
      while(iter.hasNext()){
        String key = iter.next();
        NumberedType value = m_numberedTypeMap.get(key);
        System.out.println("  ["+key+", "+value.getNumber()+"]");
      }
      try {
        throw new RuntimeException("quit");
      } catch(Exception ex){
        ex.printStackTrace();
        System.exit(0);
      }
      return 0;
    }   
  }

  public List<Type> getOrderedRefLikeTypes() {
    return m_orderedRefLikeTypes;
  }

  public List<NumberedType> getNumberedHierarchyDown(SootClass sootClass) {
    return m_hierarchyDown.get(sootClass.getType().toString());
  }

  public void addCallGraphEdge(SootMethod src, Stmt stmt, SootMethod dest) {
    Edge e = new Edge(src, stmt, dest);
    m_callGraph.addEdge(e);
  }

  public int getCallGraphEdges() {
    return m_callGraph.size();
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
    return m_rootMethod;
  }

  public List<SootMethod> getOtherEntryPoints(){
    return m_otherEntryPoints;
  }

  public CallGraph getCallGraph() {
    return m_callGraph;
  }

  public void setModifiedClasses(Set<String> modified_classes) {
    m_modifiedClasses = modified_classes;
  }
  
  public Set<String> getModifiedClasses(){
    return m_modifiedClasses;
  }

  public void outputClassTypes() {
    for(String cls : m_numberedTypeMap.keySet()){
      NumberedType ntype = m_numberedTypeMap.get(cls);
      System.out.println("num: "+ntype.getNumber()+" "+cls);
    }
  }
}
