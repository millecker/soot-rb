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

import soot.G;
import soot.Singletons;
import soot.SourceLocator;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootClass;
import soot.SootResolver;
import soot.ClassSource;
import soot.CoffiClassSource;
import soot.Scene;
import soot.Type;
import soot.ArrayType;
import soot.RefType;
import soot.options.Options;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.Pack;
import soot.PackManager;
import soot.Body;
import soot.util.Chain;
import soot.ValueBox;
import soot.Value;
import soot.Unit;
import soot.jimple.NewExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;

import java.util.List;
import java.util.LinkedList;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.jar.JarEntry;
import java.util.jar.JarInputStream;
import java.util.Arrays;
import java.util.Set;
import java.util.HashSet;
import java.util.Collection;
import java.util.Iterator;

import java.io.FileInputStream;
import java.io.InputStream;
import java.io.File;
import java.io.FileNotFoundException;

import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.PatchingChain;
import soot.Local;

import org.apache.commons.io.input.CountingInputStream;
import soot.coffi.HierarchySootClassFactory;

public class RootbeerClassLoader {

  private Map<String, DfsInfo> m_dfsInfos;
  private DfsInfo m_currDfsInfo;

  private Map<String, Set<String>> m_packageNameCache;
  private ClassHierarchy m_classHierarchy;
  private List<String> m_sourcePaths;
  private Map<String, String> m_classToFilename;
  private String m_tempFolder;
  private List<String> m_classPaths;
  private int m_loadedCount;
  private List<EntryPointDetector> m_entryDetectors;
  private List<String> m_ignorePackages;
  private List<String> m_keepPackages;
  private List<String> m_testCasePackages;
  private List<String> m_runtimeClasses;
  private List<String> m_appClasses;
  private List<String> m_entryPoints;
  private List<String> m_cudaEntryPoints;
  private List<String> m_cudaFields;
  private Set<String> m_visited;
  private String m_userJar;
  private Set<String> m_generatedMethods;
  private Set<String> m_dontDfsMethods;
  private Map<String, String> m_remapping;
  private Map<String, HierarchyValueSwitch> m_valueSwitchMap;
  private Map<String, List<String>> m_usedFields;
  private List<ConditionalCudaEntry> m_conditionalCudaEntries;
  private RemapClassName m_remapClassName;
  private boolean m_loaded;

  private Set<String> m_cgVisitedClasses;
  private Set<String> m_cgVisitedMethods;
  private List<String> m_cgMethodQueue;

  public RootbeerClassLoader(Singletons.Global g){
    m_dfsInfos = new HashMap<String, DfsInfo>();
    m_packageNameCache = new HashMap<String, Set<String>>();
    m_classHierarchy = new ClassHierarchy();
    m_classToFilename = new HashMap<String, String>();
    m_entryDetectors = new ArrayList<EntryPointDetector>();

    String home = System.getProperty("user.home");
    File soot_folder = new File(home + File.separator + ".soot" + File.separator + "rbcl_cache");
    soot_folder.mkdirs();
    m_tempFolder = soot_folder.getAbsolutePath() + File.separator;
    m_loadedCount = 0;

    m_ignorePackages = new ArrayList<String>();    
    m_keepPackages = new ArrayList<String>();
    m_testCasePackages = new ArrayList<String>();    
    m_runtimeClasses = new ArrayList<String>();

    m_appClasses = new ArrayList<String>();
    m_userJar = null;

    m_remapClassName = new RemapClassName();
    m_generatedMethods = new HashSet<String>();
    m_conditionalCudaEntries = new ArrayList<ConditionalCudaEntry>();
    m_dontDfsMethods = new HashSet<String>();
    m_valueSwitchMap = new HashMap<String, HierarchyValueSwitch>();

    m_cgVisitedClasses = new HashSet<String>();
    m_cgVisitedMethods = new HashSet<String>();
    m_cgMethodQueue = new LinkedList<String>();

    m_loaded = false;
  }

  public static RootbeerClassLoader v() { 
    return G.v().soot_rbclassload_RootbeerClassLoader(); 
  }

  public void addConditionalCudaEntry(ConditionalCudaEntry entry){
    m_conditionalCudaEntries.add(entry);
  }

  public void addDontDfsMethod(String entry){
    m_dontDfsMethods.add(entry);
  }

  public void setCudaEntryPoints(List<String> entries){
    m_cudaEntryPoints = entries;
  }

  public void setCudaFields(List<String> fields){
    m_cudaFields = fields;
  }

  public void addGeneratedMethod(String signature){
    m_generatedMethods.add(signature);
  }

  public List<String> getAllAppClasses(){
    return m_appClasses;
  }

  public ClassHierarchy getClassHierarchy(){
    return m_classHierarchy;
  }

  public void setUserJar(String filename){
    m_userJar = filename;
  }

  public void loadNecessaryClasses(){
    m_sourcePaths = SourceLocator.v().sourcePath();
    m_classPaths = SourceLocator.v().classPath();

    loadHierarchySootClasses();
    findEntryPoints();
    buildClassHierarchy();
    
    for(String entry : m_entryPoints){
      System.out.println("entry point: "+entry);
      DfsInfo dfs_info = new DfsInfo(entry);
      m_dfsInfos.put(entry, dfs_info);
      m_currDfsInfo = dfs_info;

      loadStringCallGraph();
    }


    //todo: use DfsValueSwitchCache
    //collectFields();

    //todo: look at these closely
    //cloneLibraryClasses();
    //remapFields();
    //remapTypes();

    //todo: write this. patch StringCallGraph and ClassHierarchy
    //patchState();

/*
    for(String entry : m_entryPoints){
      m_currDfsInfo = m_dfsInfos.get(entry);
      dfsForRootbeer();
    }

    Set<Type> array_types = new HashSet<Type>();
    for(DfsInfo dfs_info : m_dfsInfos.values()){
      array_types.addAll(dfs_info.getArrayTypes());
    }
*/

    //one string call graph
    //one set of all types
    //m_classHierarchy.addArrayTypes(array_types);
    m_classHierarchy.numberTypes();
    loadScene();

/*
    for(String entry : m_entryPoints){
      m_currDfsInfo = m_dfsInfos.get(entry);
      m_currDfsInfo.finalizeTypes();
    }
*/
    Scene.v().loadDynamicClasses();
  }
    
/*
  private void collectFields(){
    m_reachableFields = new HashSet<String>();
    Set<String> all = m_stringCG.getAllSignatures();
    for(String sig : all){
      collectFieldsForMethod(sig);
    }
  }

  private void collectFieldsForMethod(String sig){
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(sig);

    SootMethod method = util.getSootMethod();
                
    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

    Set<SootFieldRef> fields = value_switch.getFieldRefs();
    for(SootFieldRef ref : fields){
      String field_sig = ref.getSignature();
      if(m_reachableFields.contains(field_sig) == false){
        m_reachableFields.add(field_sig);          
      }
    }
  }
*/
/*
  private List<String> getReachableClasses(){
    List<String> ret = new ArrayList<String>();
    Set<String> ret_set = new HashSet<String>();

    Set<String> all_method_sigs = m_stringCG.getAllSignatures();
    //collect class names and main_classes
    for(String method_sig : all_method_sigs){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(method_sig);
      util.remap();
      String class_name = util.getClassName();
      if(ret_set.contains(class_name) == false){
        ret_set.add(class_name);
      }
    }  

    //collect class names from reachable fields
    for(String field_sig : m_reachableFields){
      FieldSignatureUtil util = new FieldSignatureUtil();
      util.parse(field_sig);
      util.remap();

      String declaring_class = util.getDeclaringClass();
      if(ret_set.contains(declaring_class) == false){
        ret_set.add(declaring_class);
      }
      String field_type = util.getType();
      if(ret_set.contains(field_type) == false){
        ret_set.add(field_type);
      }
    }

    //collect class names from generated classes
    List<SootClass> added_classes = Scene.v().getGeneratedClasses();
    for(SootClass added : added_classes){
      String name = added.getName();
      if(ret_set.contains(name) == false){
        ret_set.add(name);
      }
    }

    ret.addAll(ret_set);
    return ret;    
  }

  private void findFieldsReachableFromGeneratedMethods(){
    for(String sig : m_generatedMethods){
      collectFieldsForMethod(sig); 
    }
  }

  public List<String> getClassesToOutput(){
    List<String> ret = new ArrayList<String>();

    Set<String> main_classes = new HashSet<String>();
    Set<String> all_method_sigs = m_stringCG.getAllSignatures();

    findFieldsReachableFromGeneratedMethods();
    List<String> reachable_classes = getReachableClasses();

    //collect class names and main_classes
    for(String class_name : reachable_classes){
      SootClass soot_class = Scene.v().getSootClass(class_name);
      String subsig = "void main(java.lang.String[])";

      if(soot_class.declaresMethod(subsig)){
        if(main_classes.contains(class_name) == false){
          main_classes.add(class_name);
        }
      }
    }  

    //find <init> of main classes and don't delete them
    for(String main_class : main_classes){
      SootClass soot_class = Scene.v().getSootClass(main_class);
      if(soot_class.declaresMethod("void <init>()")){
        SootMethod init_method = soot_class.getMethod("void <init>()");
        String init_sig = init_method.getSignature();
        if(all_method_sigs.contains(init_sig) == false){
          all_method_sigs.add(init_sig);
        }
      }
    }

    //trim things in classes that are not reachable
    for(String class_name : reachable_classes){
        
      //don't trim the runtime classes in the keep_packages
      if(isKeepPackage(class_name)){
        continue;
      }

      //don't trim any named runtime classes
      if(m_runtimeClasses.contains(class_name)){
        continue;
      }

      SootClass soot_class = Scene.v().getSootClass(class_name);
      List<SootMethod> methods = soot_class.getMethods();
      List<SootMethod> methods_to_delete = new ArrayList<SootMethod>();
      for(SootMethod method : methods){
        String method_sig = method.getSignature();
        //don't delete generated methods
        if(m_generatedMethods.contains(method_sig)){
          continue;
        }
        if(all_method_sigs.contains(method_sig) == false){
          methods_to_delete.add(method);
        } else {
          //load the body in case it hasn't
          if(method.isConcrete()){
            method.retrieveActiveBody();
          }
        }
      }
      for(SootMethod to_delete : methods_to_delete){
        soot_class.removeMethod(to_delete);
      }
      List<SootField> fields_to_delete = new ArrayList<SootField>();
      Iterator<SootField> field_iter = soot_class.getFields().iterator();
      while(field_iter.hasNext()){
        SootField curr_field = field_iter.next();
        String field_sig = curr_field.getSignature();
        if(m_reachableFields.contains(field_sig) == false){
          fields_to_delete.add(curr_field);
        }
      }
      for(SootField to_delete : fields_to_delete){
        soot_class.removeField(to_delete);
      }
    }

    //load bodies for all methods
    Set<String> body_load_sigs = new HashSet<String>();
    body_load_sigs.addAll(m_generatedMethods);
    body_load_sigs.addAll(all_method_sigs);
    for(String sig : body_load_sigs){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(sig);

      SootMethod method = util.getSootMethod();
      if(method.isConcrete() && method.hasActiveBody() == false){
        method.retrieveActiveBody();
      }
    }

    return reachable_classes;
  }
*/
  public void setLoaded(){
    m_loaded = true;
  }

  private void loadStringCallGraph(){
    String entry = m_currDfsInfo.getRootMethodSignature();

    System.out.println("loading forward string call graph for: "+entry+"...");
    m_cgMethodQueue.add(entry);
    m_cgVisitedMethods.add(entry);

    m_currDfsInfo.getStringCallGraph().addEntryPoint(entry);

    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(entry);
    HierarchySootClass entry_class = m_classHierarchy.getHierarchySootClass(util.getClassName());
    HierarchySootMethod entry_ctor = entry_class.findMethodBySubSignature("void <init>()");
    m_cgMethodQueue.add(entry_ctor.getSignature());
    m_cgVisitedMethods.add(entry_ctor.getSignature());

    processForwardStringCallGraphQueue();

    System.out.println("loading reverse string call graph for: "+entry+"...");
    Set<String> reachable = new HashSet<String>();
    Set<String> unvisited = new HashSet<String>();
    reachable.add(entry_ctor.getSignature());
    reachable.add(m_currDfsInfo.getRootMethodSignature());

    int prev_size = -1;
    while(prev_size != reachable.size()){
      prev_size = reachable.size();
      unvisited.clear();
      for(String class_name : m_appClasses){
        HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
        List<HierarchySootMethod> methods = hclass.getMethods();
        for(HierarchySootMethod method : methods){
          String method_sig = method.getSignature();
          reverseStringGraphVisit(method_sig, reachable);   
        }
      }
    }

    //System.out.println("StringCallGraph: "+m_currDfsInfo.getStringCallGraph().toString());
  }

  private void processForwardStringCallGraphQueue(){
    MethodSignatureUtil util = new MethodSignatureUtil();
    while(m_cgMethodQueue.isEmpty() == false){
      String bfs_entry = m_cgMethodQueue.get(0);
      m_cgMethodQueue.remove(0);

      util.parse(bfs_entry);

      String class_name = util.getClassName();
      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
      if(hclass == null){
        continue;
      }

      HierarchySootMethod hmethod = hclass.findMethodBySubSignature(util.getSubSignature());            
      if(hmethod == null){
        continue;
      }

      if(hmethod.isConcrete() == false){
        continue;
      }

      System.out.println("processForwardStringCallGraphQueue: "+bfs_entry);

      //add virtual methods to queue
      List<String> virt_methods = m_classHierarchy.getVirtualMethods(bfs_entry);
      for(String signature : virt_methods){
        if(m_dontDfsMethods.contains(signature)){
          continue;
        }

        if(m_cgVisitedMethods.contains(signature)){
          continue;
        }
        m_cgVisitedMethods.add(signature);
        //System.out.println("loadStringGraph adding virtual_method to queue: "+signature);
        m_cgMethodQueue.add(signature);
      }

      //add bfs methods to queue
      HierarchyValueSwitch value_switch = getValueSwitch(bfs_entry);
      for(String dest_sig : value_switch.getMethodRefs()){
        if(m_dontDfsMethods.contains(dest_sig)){
          continue;
        }

        if(m_cgVisitedMethods.contains(dest_sig)){
          continue;
        }
        m_cgVisitedMethods.add(dest_sig);
        m_currDfsInfo.getStringCallGraph().addEdge(bfs_entry, dest_sig);
        //System.out.println("loadStringGraph addEdge: "+bfs_entry+"->"+dest_sig);
        m_cgMethodQueue.add(dest_sig);        
      }

      //add <clinit> of class_refs
      Set<String> class_refs = value_switch.getClasses();
      for(String class_ref : class_refs){
        HierarchySootClass clinit_class = m_classHierarchy.getHierarchySootClass(class_ref);
        if(clinit_class == null){
          continue;
        }
        HierarchySootMethod clinit_method = clinit_class.findMethodBySubSignature("void <clinit>()");
        if(clinit_method == null){
          continue;
        }

        String clinit_sig = clinit_method.getSignature();

        if(m_dontDfsMethods.contains(clinit_sig)){
          continue;
        }

        if(m_cgVisitedMethods.contains(clinit_sig)){
          continue;
        }
        m_cgVisitedMethods.add(clinit_sig);
        m_cgMethodQueue.add(clinit_sig);   
      }

      if(m_cgVisitedClasses.contains(class_name)){
        continue;
      }
      m_cgVisitedClasses.add(class_name);

      //add <init> and <clinit> to queue
      List<HierarchySootMethod> methods = hclass.getMethods();
      for(HierarchySootMethod method : methods){
        String name = method.getName();
        //<init> shouldn't really be included here. 
        //this is because in rootbeer reflection is
        //used to load methods for tests. in the future
        //we could use symbolic execution to get by
        //reflection.
        if(name.equals("<init>") || name.equals("<clinit>")){
          //System.out.println("loadStringGraph adding ctor: "+method.getSignature());

          if(m_dontDfsMethods.contains(method.getSignature())){
            continue;
          }

          if(m_cgVisitedMethods.contains(method.getSignature())){
            continue;
          }
          m_cgVisitedMethods.add(method.getSignature());
          m_cgMethodQueue.add(method.getSignature());          
        }
      }
    }
  }

  private void reverseStringGraphVisit(String method_sig, Set<String> reachable){
    MethodSignatureUtil util = new MethodSignatureUtil();
    HierarchyValueSwitch value_switch = getValueSwitch(method_sig);
    for(String dest_sig : value_switch.getMethodRefs()){
      if(m_dontDfsMethods.contains(dest_sig)){
        continue;
      }
      if(reachable.contains(dest_sig)){
        //System.out.println("loadStringGraph addEdge: "+method_sig+"->"+dest_sig);
        m_currDfsInfo.getStringCallGraph().addEdge(method_sig, dest_sig);
        reachable.add(method_sig);

        //add virtual methods to queue
        List<String> virt_methods = m_classHierarchy.getVirtualMethods(method_sig);
        for(String virt_method : virt_methods){
          if(reachable.contains(virt_method) == false){
            reachable.add(virt_method);
            reverseStringGraphVisit(virt_method, reachable);
          }
        }

        //add <init> and <clinit> to reachable
        util.parse(method_sig);
        String class_name = util.getClassName();
        HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
        List<HierarchySootMethod> methods = hclass.getMethods();
        for(HierarchySootMethod method : methods){
          if(m_dontDfsMethods.contains(method.getSignature())){
            continue;
          }

          if(m_cgVisitedMethods.contains(method.getSignature())){
            continue;
          }
          m_cgVisitedMethods.add(method.getSignature());

          String name = method.getName();
          //<init> shouldn't really be included here. 
          //this is because in rootbeer reflection is
          //used to load methods for tests. in the future
          //we could use symbolic execution to get by
          //reflection.
          if(name.equals("<init>") || name.equals("<clinit>")){
            //System.out.println("loadStringGraph adding ctor: "+method.getSignature());
            reachable.add(method.getSignature());          
          }
        }
      } 
    }

    //add <clinit> of class_refs
    Set<String> class_refs = value_switch.getClasses();
    for(String class_ref : class_refs){
      HierarchySootClass clinit_class = m_classHierarchy.getHierarchySootClass(class_ref);
      if(clinit_class == null){
        continue;
      }

      HierarchySootMethod clinit_method = clinit_class.findMethodBySubSignature("void <clinit>()");
      if(clinit_method == null){
        continue;
      }

      String clinit_sig = clinit_method.getSignature();

      if(m_dontDfsMethods.contains(clinit_sig)){
        continue;
      }

      if(m_cgVisitedMethods.contains(clinit_sig)){
        continue;
      }
      m_cgVisitedMethods.add(clinit_sig);
      m_cgMethodQueue.add(clinit_sig);   
    } 
    processForwardStringCallGraphQueue();
  }

  private void loadScene(){
    System.out.println("loading scene...");

    System.out.println("creating empty classes according to type number...");
    //create all empty classes from lowest number to highest
    StringToType string_to_type = new StringToType();
    List<NumberedType> numbered_types = m_classHierarchy.getNumberedTypes();
    for(NumberedType ntype : numbered_types){
      String type_string = ntype.getType();
      if(string_to_type.isRefType(type_string) == false){
        continue;
      }      
      if(string_to_type.isArrayType(type_string)){
        type_string = string_to_type.getBaseType(type_string);
      }
      SootClass emptyClass = new SootClass(type_string);

      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(type_string);
      if(hclass.hasSuperClass()){
        SootClass superClass = Scene.v().getSootClass(hclass.getSuperClass());
        emptyClass.setSuperclass(superClass);
      }
      for(String iface : hclass.getInterfaces()){
        SootClass ifaceClass = Scene.v().getSootClass(iface);
        emptyClass.addInterface(ifaceClass);
      }
    }

    System.out.println("collecting fields for classes and adding to declaring class...");
    //collect fields for classes and add to declaring_class
    m_usedFields = new HashMap<String, List<String>>();
    Set<String> all_sigs = m_currDfsInfo.getStringCallGraph().getAllSignatures();
    for(String signature : all_sigs){
      HierarchyValueSwitch value_switch = getValueSwitch(signature);
      for(String field_ref : value_switch.getFieldRefs()){
        FieldSignatureUtil util = new FieldSignatureUtil();
        util.parse(field_ref);

        String class_name = util.getDeclaringClass();
        SootClass declaring_class = Scene.v().getSootClass(class_name);
        Type field_type = string_to_type.convert(util.getType());
        SootField new_field = new SootField(util.getName(), field_type);
        declaring_class.addField(new_field);
      }
    }

    System.out.println("adding empty methods...");
    //add empty methods
    for(String signature : all_sigs){
      
      
    }

    System.out.println("adding method bodies...");
    //add method bodies
  }

  private HierarchyValueSwitch getValueSwitch(String signature){
    if(m_valueSwitchMap.containsKey(signature)){
      return m_valueSwitchMap.get(signature);
    } else {
      HierarchyValueSwitch value_switch = new HierarchyValueSwitch();
      value_switch.run(signature);
      m_valueSwitchMap.put(signature, value_switch);
      return value_switch;
    }
  }

  private void sortApplicationClasses(){
    //System.out.println("sorting application classes...");
    //java.util.Collections.sort(m_appClasses);
  }

  public boolean isLoaded(){
    return m_loaded;
  }

/*
  private void cloneLibraryClasses(){
    System.out.println("cloning library classes...");
    m_remapping = new HashMap<String, String>();

    BuiltInRemaps built_in = new BuiltInRemaps();

    Set<String> lib_classes = m_stringCG.getLibraryClasses();
    String prefix = Options.v().rbcl_remap_prefix();

    for(String lib_class : lib_classes){
      if(built_in.containsKey(lib_class)){
        m_remapping.put(lib_class, built_in.get(lib_class));
        continue;
      }

      if(m_remapClassName.shouldMap(lib_class) == false){
        m_remapping.put(lib_class, lib_class);
        continue;
      }

      String new_name = prefix+lib_class;
    
      SootClass soot_class = Scene.v().getSootClass(lib_class);
      CloneClass cloner = new CloneClass();
      SootClass new_class = cloner.execute(soot_class, new_name, m_stringCG, m_reachableFields);

      Scene.v().addGeneratedClass(new_class);
      m_remapping.put(lib_class, new_name);
    }
  }

  private void remapFields(){
    System.out.println("remapping fields...");
    Set<String> lib_classes = m_stringCG.getLibraryClasses();
    BuiltInRemaps built_ins = new BuiltInRemaps();

    for(String field_sig : m_reachableFields){
      FieldSignatureUtil util = new FieldSignatureUtil();
      util.parse(field_sig);

      String declaring_class = util.getDeclaringClass();
      if(built_ins.containsKey(declaring_class)){
        if(built_ins.isRealMapping(declaring_class)){
          continue;
        }
      }

      if(isKeepPackage(declaring_class)){
        continue;
      }

      if(lib_classes.contains(declaring_class)){
        String new_class = m_remapClassName.getMapping(declaring_class);
        util.setDeclaringClass(new_class);
      }

      StringToType converter = new StringToType();
      Type field_type = converter.toType(util.getType());

      SootField soot_field = util.getSootField();
      if(field_type instanceof RefType){
        String type_string = util.getType();
        if(lib_classes.contains(type_string)){
          String new_type_string = m_remapClassName.getMapping(type_string);
          Type new_type = converter.toType(new_type_string);
          soot_field.setType(new_type);          
        }
      } else if(field_type instanceof ArrayType){
        ArrayType array_type = (ArrayType) field_type;
        Type base_type = array_type.baseType;
        if(base_type instanceof RefType){
          RefType ref_type = (RefType) base_type;
          String class_name = ref_type.getClassName();
          if(lib_classes.contains(class_name)){
            String new_type_string = m_remapClassName.getMapping(class_name);
            Type new_base_type = converter.toType(new_type_string);
            Type new_type = ArrayType.v(new_base_type, array_type.numDimensions);
            soot_field.setType(new_type); 
          }
        }
      }
    }
  }

  private String remapClassOfMethodSignature(String signature){
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);
 
    String class_name = util.getClassName();
    String new_class_name = m_remapClassName.getMapping(class_name);
    util.setClassName(new_class_name);        

    return util.getSignature();
  }

  private void remapTypes(){    
    System.out.println("remapping types...");
    Iterator<SootClass> iter = Scene.v().getClasses().snapshotIterator();

    //remapping superclass, interfaces and outerclass
    while(iter.hasNext()){
      SootClass soot_class = iter.next();
      if(soot_class.hasSuperclass()){
        SootClass super_class = soot_class.getSuperclass();
        super_class = m_remapClassName.getMapping(super_class);
        soot_class.setSuperclass(super_class);
      }
      Chain<SootClass> interfaces = soot_class.getInterfaces();
      if(interfaces.size() != 0){
        SootClass curr = interfaces.getFirst();
        while(curr != null){
          SootClass next = interfaces.getSuccOf(curr);
          SootClass remapped = m_remapClassName.getMapping(curr);
          if(remapped.equals(curr) == false){
            interfaces.swapWith(curr, remapped);
          }
          curr = next;  
        }
      }
      if(soot_class.hasOuterClass()){
        SootClass outer_class = soot_class.getOuterClass();
        outer_class = m_remapClassName.getMapping(outer_class);
        soot_class.setOuterClass(outer_class);        
      }
    }

    //remapping arguments of all signatures from string call graph
    BuiltInRemaps built_ins = new BuiltInRemaps();
    Set<String> all = m_stringCG.getAllSignatures();
    for(String signature : all){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);

      String class_name = util.getClassName();
      boolean throw_error = true;
      if(built_ins.isRealMapping(class_name)){
        throw_error = false;
      }

      String declaring_class = util.getClassName();
      if(isKeepPackage(declaring_class)){
        continue;
      }

      try {
        signature = remapClassOfMethodSignature(signature);      
        util.parse(signature);

        SootMethod soot_method = util.getSootMethod();

        RemapMethod remapper = new RemapMethod();
        remapper.fixArguments(soot_method);
      } catch(RuntimeException ex){
        if(throw_error){
          throw ex;
        }
      }
    }

    //remapping bodies
    for(String signature : all){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);

      String class_name = util.getClassName();
      boolean throw_error = true;
      if(built_ins.isRealMapping(class_name)){
        throw_error = false;
      }

      String declaring_class = util.getClassName();
      if(isKeepPackage(declaring_class)){
        continue;
      }

      try {
        util.remap();

        SootMethod soot_method = util.getSootMethod();
  
        RemapMethod remapper = new RemapMethod();
        remapper.visit(soot_method);
      } catch(RuntimeException ex){
        if(throw_error){
          throw ex;
        }
      }
    }
  }
*/

  private boolean isKeepPackage(String declaring_class){
    for(String keep_package : m_keepPackages){
      if(declaring_class.startsWith(keep_package)){
        return true;
      }
    }
    return false;
  }
/*
  private void dfsForRootbeer(){
    SootMethod soot_method = m_currDfsInfo.getRootMethod();
    
    Set<String> visited = new HashSet<String>();
    System.out.println("doing rootbeer dfs: "+soot_method.getSignature());
    List<String> queue = new LinkedList<String>();
    queue.add(soot_method.getSignature());

    for(String cuda_entry : m_cudaEntryPoints){
      queue.add(cuda_entry);    
    }

    for(ConditionalCudaEntry conditional_entry : m_conditionalCudaEntries){
      if(conditional_entry.condition(m_currDfsInfo)){
        queue.add(conditional_entry);
      }
    }

    while(queue.isEmpty() == false){
      String curr = queue.get(0);
      queue.remove(0);
      doDfs(curr, queue, visited);
    }

    for(String cuda_field : m_cudaFields){
      FieldSignatureUtil futil = new FieldSignatureUtil();
      futil.parse(cuda_field);
      
      SootField soot_field = futil.getSootField();
      m_currDfsInfo.addField(soot_field);
    }
      
    System.out.println("building class hierarchy for: "+soot_method.getSignature()+"...");
    m_currDfsInfo.expandArrayTypes();
  }
*/

  public void applyOptimizations(){
    throw new UnsupportedOperationException();
/*
    Pack jop = PackManager.v().getPack("jop");
    
    for(String entry : m_entryPoints){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(entry);
      util.remap();

      SootMethod soot_method = util.getSootMethod();
      if(soot_method.getName().equals("gpuMethod") == false){
        continue;
      }

      m_currDfsInfo = m_dfsInfos.get(soot_method.getSignature());
      Set<String> methods = m_currDfsInfo.getMethods();
      for(String curr_sig : methods){
        util.parse(curr_sig);
        SootClass soot_class = Scene.v().getSootClass(util.getClassName());
        SootMethod curr_method = soot_class.getMethod(util.getMethodSubSignature());
        if(curr_method.isConcrete()){
          Body body = curr_method.retrieveActiveBody();
          jop.apply(body);
        }
      }
    }
*/
  }

  public List<SootMethod> getEntryPoints(){
    List<SootMethod> ret = new ArrayList<SootMethod>();
    
    for(String entry : m_entryPoints){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(entry);
      
      String method = util.getMethodName();
      if(method.equals("gpuMethod")){
        ret.add(util.getSootMethod());
      }
    }
    return ret;
  }

  public void loadDfsInfo(SootMethod entry){
    String sig = entry.getSignature();
    m_currDfsInfo = m_dfsInfos.get(sig);
  }

  public void addEntryPointDetector(EntryPointDetector detector){
    m_entryDetectors.add(detector);
  }

  private void loadHierarchySootClasses(){
    HierarchySootClassFactory hclassFactory = new HierarchySootClassFactory();
    List<String> paths = SourceLocator.v().classPath();
    List<String> local_paths = new ArrayList<String>();
    local_paths.addAll(paths);
    if(m_userJar != null){
      local_paths.add(m_userJar);
    }
    String[] to_cache = new String[local_paths.size()];
    to_cache = local_paths.toArray(to_cache);
    Arrays.sort(to_cache);
    for(String jar : to_cache){
      if(jar.endsWith(".jar")){
        File file = new File(jar);
        if(file.exists() == false){
          continue;
        }
        System.out.println("caching package names for: "+jar);
        try {
          CountingInputStream count_stream = new CountingInputStream(new FileInputStream(jar));
          JarInputStream jin = new JarInputStream(count_stream);
          while(true){
            JarEntry entry = jin.getNextJarEntry();
            if(entry == null){
              break;
            }

            if(entry.getCompressedSize() == -1 && entry.getSize() == -1){
              continue;
            } 

            String name = entry.getName();
            String package_name;
            if(name.endsWith(".class")){
              String filename = name;
              name = name.replace(".class", "");
              name = name.replace("/", ".");
              package_name = getPackageName(name);

              HierarchySootClass hierarchy_class = hclassFactory.create(filename, jin);
              m_classHierarchy.put(name, hierarchy_class);

              if(jar.equals(m_userJar)){
                m_appClasses.add(name);
              }
            } else {
              name = name.replace("/", ".");
              package_name = name.substring(0, name.length()-1);
            }
            if(m_packageNameCache.containsKey(package_name)){
              Set<String> jars = m_packageNameCache.get(package_name);
              if(jars.contains(jar) == false){
                jars.add(jar);
              }
            } else {
              Set<String> jars = new HashSet<String>();
              jars.add(jar);
              m_packageNameCache.put(package_name, jars);
            }
          }
          jin.close();
        } catch(Exception ex){
          ex.printStackTrace();
        }
      }
    }
  }

  private void buildClassHierarchy(){
    System.out.println("building class hierarchy...");
    m_classHierarchy.build();
    //System.out.println(m_classHierarchy.toString());
  }

  private String getPackageName(String className) {
    String[] tokens = className.split("\\.");
    String ret = "";
    for(int i = 0; i < tokens.length - 1; ++i){
      ret += tokens[i];
      if(i < tokens.length - 2){
        ret += ".";
      }
    }
    return ret;
  }

  private void loadBuiltIns(){
    //copied from soot.Scene.addSootBasicClasses()

    System.out.println("loading built-ins...");
    addBasicClass("java.lang.Object");
	  addBasicClass("java.lang.Class");

	  addBasicClass("java.lang.Void");
	  addBasicClass("java.lang.Boolean");
	  addBasicClass("java.lang.Byte");
	  addBasicClass("java.lang.Character");
	  addBasicClass("java.lang.Short");
	  addBasicClass("java.lang.Integer");
	  addBasicClass("java.lang.Long");
	  addBasicClass("java.lang.Float");
	  addBasicClass("java.lang.Double");

	  addBasicClass("java.lang.String");
	  addBasicClass("java.lang.StringBuffer");

	  addBasicClass("java.lang.Error");
	  addBasicClass("java.lang.AssertionError");
	  addBasicClass("java.lang.Throwable");
	  addBasicClass("java.lang.NoClassDefFoundError");
	  addBasicClass("java.lang.ExceptionInInitializerError");
	  addBasicClass("java.lang.RuntimeException");
	  addBasicClass("java.lang.ClassNotFoundException");
	  addBasicClass("java.lang.ArithmeticException");
	  addBasicClass("java.lang.ArrayStoreException");
	  addBasicClass("java.lang.ClassCastException");
	  addBasicClass("java.lang.IllegalMonitorStateException");
	  addBasicClass("java.lang.IndexOutOfBoundsException");
	  addBasicClass("java.lang.ArrayIndexOutOfBoundsException");
	  addBasicClass("java.lang.NegativeArraySizeException");
	  addBasicClass("java.lang.NullPointerException");
	  addBasicClass("java.lang.InstantiationError");
	  addBasicClass("java.lang.InternalError");
	  addBasicClass("java.lang.OutOfMemoryError");
	  addBasicClass("java.lang.StackOverflowError");
	  addBasicClass("java.lang.UnknownError");
	  addBasicClass("java.lang.ThreadDeath");
	  addBasicClass("java.lang.ClassCircularityError");
	  addBasicClass("java.lang.ClassFormatError");
	  addBasicClass("java.lang.IllegalAccessError");
	  addBasicClass("java.lang.IncompatibleClassChangeError");
	  addBasicClass("java.lang.LinkageError");
	  addBasicClass("java.lang.VerifyError");
	  addBasicClass("java.lang.NoSuchFieldError");
	  addBasicClass("java.lang.AbstractMethodError");
	  addBasicClass("java.lang.NoSuchMethodError");
	  addBasicClass("java.lang.UnsatisfiedLinkError");

	  addBasicClass("java.lang.Thread");
	  addBasicClass("java.lang.Runnable");
	  addBasicClass("java.lang.Cloneable");
	  addBasicClass("java.io.Serializable");	
	  addBasicClass("java.lang.ref.Finalizer");
  }

  private void addBasicClass(String class_name) {
    addBasicClass(class_name, SootClass.HIERARCHY);
  }

  private void addBasicClass(String class_name, int level) {
    resolveClass(class_name, level);
  }

  public void resolveClass(String class_name, int level){
    SootResolver.v().resolveClass(class_name, level);
  }

  private boolean findClass(Collection<String> jars, String filename, String class_name) throws Exception {
    for(String jar : jars){
      JarInputStream fin = new JarInputStream(new FileInputStream(jar));
      while(true){
        JarEntry entry = fin.getNextJarEntry();
        if(entry == null){
          break;
        }
        if(entry.getName().equals(filename) == false){
          continue;
        }
        m_classToFilename.put(class_name, m_tempFolder + filename);
        WriteJarEntry writer = new WriteJarEntry();
        writer.write(entry, fin, m_tempFolder);
        fin.close();
        return true;
      }
      fin.close();
    }
    return false;
  }

  private String classNameToFilename(String className){
    String filename = className.replace(".", "/");
    filename += ".class";
    return filename;
  }

  public void findClass(String className) throws Exception {
    String package_name = getPackageName(className);
    String filename = className.replace(".", "/");
    filename += ".class";
    Set<String> jar_cache = m_packageNameCache.get(package_name);
    if(jar_cache == null){
      if(package_name.equals("")){
        findClass(m_classPaths, filename, className);
        return;
      } else {
        return;
      }
    }
    if(findClass(jar_cache, filename, className)){
      return;
    }
    //maybe there is a class in the default package, try all if not found in cache.
    if(package_name.equals("")){
      findClass(m_classPaths, filename, className);
    }
  }

  public ClassSource getClassSource(String class_name) {
    String filename = classNameToFilename(class_name);

    File file = new File(m_tempFolder + filename);
    if(file.exists()){
      m_classToFilename.put(class_name, file.getAbsolutePath());
    }

    if(m_classToFilename.containsKey(class_name) == false){
      try {
        findClass(class_name);
      } catch(Exception ex){
        //ignore
      }
    }

    m_loadedCount++;
    //System.out.println("loading: "+class_name+" count: "+m_loadedCount);

    if(m_classToFilename.containsKey(class_name) == false){
      return null;
    }

    try {
      String full_filename = m_classToFilename.get(class_name);
      //System.out.println("loading: "+class_name+" from: "+full_filename);
      InputStream stream = new FileInputStream(full_filename);
		  if(stream == null){
        return null;
      }
		  return new CoffiClassSource(class_name, stream);
    } catch(FileNotFoundException ex){
      ex.printStackTrace();
      return null;
    }
  }


  public int getClassNumber(SootClass soot_class){
    return getClassNumber(soot_class.getName());
  }

  public int getClassNumber(String type_string){
    NumberedType ntype = m_classHierarchy.getNumberedType(type_string);
    return (int) ntype.getNumber();
  }

  private void findEntryPoints(){
    System.out.println("finding entry points...");
    m_entryPoints = new ArrayList<String>();
    for(String app_class : m_appClasses){
      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(app_class);
      List<HierarchySootMethod> methods = hclass.getMethods();
      for(HierarchySootMethod method : methods){
        for(EntryPointDetector detector : m_entryDetectors){
          detector.testEntryPoint(method);
        }
      }
    }
    for(EntryPointDetector detector : m_entryDetectors){
      m_entryPoints.addAll(detector.getEntryPoints());
    }
  }

/*
  private void doDfs(String method, List<String> queue, Set<String> visited){  
    if(m_dontDfsMethods.contains(method)){
      return;
    }

    List<String> virt_methods = m_classHierarchy.getVirtualMethods(method.getSignature());
    for(String virt_method : virt_methods){
      if(method.getSignature().equals(virt_method)){
        continue;
      }
    
      if(visited.contains(virt_method) == false){
        queue.add(virt_method);
      }
    }

    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(method);
    if(ignorePackage(util.getClassName()){
      return;
    }

    if(isKeepPackage(util.getClassName()){
      return;
    }

    if(visited.contains(method)){
      return;
    }
    visited.add(method);
    
    //System.out.println("doDfs: "+signature);

    m_currDfsInfo.addMethod(method);
    m_currDfsInfo.addType(soot_class.getType());
    
    if(method.isConcrete() == false){
      return;
    }

    DfsValueSwitch value_switch = getDfsValueSwitch(signature);

    Set<Type> all_types = value_switch.getAllTypes();
    for(Type type : all_types){
      m_currDfsInfo.addType(type);
    }

    Set<SootFieldRef> fields = value_switch.getFieldRefs();
    for(SootFieldRef ref : fields){
      m_currDfsInfo.addType(ref.type());
      
      SootField field = ref.resolve();
      m_currDfsInfo.addField(field);
    }
    
    Set<Type> instance_ofs = value_switch.getInstanceOfs();
    for(Type type : instance_ofs){
      m_currDfsInfo.addInstanceOf(type);
    }

    Set<DfsMethodRef> methods = value_switch.getMethodRefs();
    for(DfsMethodRef ref : methods){
      SootMethodRef mref = ref.getSootMethodRef();
      SootClass method_class = mref.declaringClass();
      SootMethod dest = mref.resolve();     

      if(visited.contains(dest.getSignature()) == false){
        queue.add(dest);
      }
    }
  }

  private void addType(Type type) {
    List<Type> queue = new LinkedList<Type>();
    queue.add(type);
    while(queue.isEmpty() == false){
      Type curr = queue.get(0);
      queue.remove(0);
      
      if(m_currDfsInfo.containsType(curr)){
        continue;
      }
        
      SootClass type_class = findTypeClass(curr);
      if(type_class == null){
        m_currDfsInfo.addType(curr);
        continue;
      }
      
      type_class = SootResolver.v().resolveClass(type_class.getName(), SootClass.HIERARCHY);

      if(isKeepPackage(type_class.getName())){
        continue;
      }
      
      m_currDfsInfo.addType(curr);

      if(type_class.hasSuperclass()){
        queue.add(type_class.getSuperclass().getType());
      }
      
      if(type_class.hasOuterClass()){
        queue.add(type_class.getOuterClass().getType());
      }

      Iterator<SootClass> iter0 = type_class.getInterfaces().iterator();
      while(iter0.hasNext()){
        SootClass soot_class = iter0.next();
        addType(soot_class.getType());
      }

      Iterator<SootField> iter = type_class.getFields().iterator();
      while(iter.hasNext()){
        SootField curr_field = iter.next();
        String field_sig = curr_field.getSignature();
        
        Type field_type = curr_field.getType();
        addType(field_type);
        addType(curr_field.getDeclaringClass().getType());
      }
    }
  }
*/
  private SootClass findTypeClass(Type type){
    if(type instanceof ArrayType){
      ArrayType array_type = (ArrayType) type;
      return findTypeClass(array_type.baseType);
    } else if(type instanceof RefType){
      RefType ref_type = (RefType) type;
      return ref_type.getSootClass();
    } else {
      //PrimType and VoidType
      return null;
    } 
  }

  private boolean shouldDfsMethod(SootMethod method){
    SootClass soot_class = method.getDeclaringClass();
    String pkg = soot_class.getPackageName();
    if(ignorePackage(pkg)){
      return false;
    } 
    return true;
  }

  private boolean ignorePackage(String class_name) {
    for(String runtime_class : m_runtimeClasses){
      if(class_name.equals(runtime_class)){
        return false;
      }
    }
    for(String keep_package : m_keepPackages){
      if(class_name.startsWith(keep_package)){
        return false;
      }
    }
    for(String test_package : m_testCasePackages){
      if(class_name.startsWith(test_package)){
        return false;
      }
    }
    for(String ignore_package : m_ignorePackages){
      if(class_name.startsWith(ignore_package)){
        return true;
      }
    }
    return false;
  }

  public void addRuntimeClass(String class_name){
    m_runtimeClasses.add(class_name);
  }

  public void addIgnorePackage(String pkg_name){
    m_ignorePackages.add(pkg_name);
  }

  public void addKeepPackages(String pkg_name){
    m_keepPackages.add(pkg_name);
  }

  public void addTestCasePackage(String pkg_name){
    m_testCasePackages.add(pkg_name);
  }

  public SootMethod findMethod(SootClass curr, String subsig){
    while(true){
      if(curr.declaresMethod(subsig)){
        return curr.getMethod(subsig);
      }
      if(curr.hasSuperclass()){
        curr = curr.getSuperclass();
      } else {
        return null;
      }
    }
  }

  public DfsInfo getDfsInfo(){
    return m_currDfsInfo;
  }

}
