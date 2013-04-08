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
  private List<String> m_signaturesClasses;
  private List<String> m_appClasses;
  private List<String> m_entryPoints;
  private List<String> m_cudaFields;
  private Set<String> m_visited;
  private String m_userJar;
  private Set<String> m_generatedMethods;
  private Set<String> m_dontDfsMethods;
  private Set<String> m_followClasses;
  private Set<String> m_followSignatures;
  private Set<String> m_newInvokes;
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
    m_signaturesClasses = new ArrayList<String>();

    m_appClasses = new ArrayList<String>();
    m_userJar = null;

    m_remapClassName = new RemapClassName();
    m_generatedMethods = new HashSet<String>();
    m_conditionalCudaEntries = new ArrayList<ConditionalCudaEntry>();
    m_dontDfsMethods = new HashSet<String>();
    m_followClasses = new HashSet<String>();
    m_followSignatures = new HashSet<String>();
    m_newInvokes = new HashSet<String>();
    m_valueSwitchMap = new HashMap<String, HierarchyValueSwitch>();

    m_cgVisitedClasses = new HashSet<String>();
    m_cgVisitedMethods = new HashSet<String>();
    m_cgMethodQueue = new LinkedList<String>();

    m_loaded = false;

    addBuiltIns();
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

  public void addFollowClass(String class_name){
    m_followClasses.add(class_name);
  }

  public void addFollowSignature(String signature){
    m_followSignatures.add(signature);
  }

  public void addNewInvoke(String class_name){
    m_newInvokes.add(class_name);
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

  private void addBuiltIns(){
    //taken from soot.Scene:1094
    addSignaturesClass("java.lang.Object");
	  addSignaturesClass("java.lang.Class");

	  addSignaturesClass("java.lang.Void");
	  addSignaturesClass("java.lang.Boolean");
	  addSignaturesClass("java.lang.Byte");
	  addSignaturesClass("java.lang.Character");
	  addSignaturesClass("java.lang.Short");
	  addSignaturesClass("java.lang.Integer");
	  addSignaturesClass("java.lang.Long");
	  addSignaturesClass("java.lang.Float");
	  addSignaturesClass("java.lang.Double");

	  addSignaturesClass("java.lang.String");
	  addSignaturesClass("java.lang.StringBuffer");

	  addSignaturesClass("java.lang.Error");
	  addSignaturesClass("java.lang.AssertionError");
	  addSignaturesClass("java.lang.Throwable");
	  addSignaturesClass("java.lang.NoClassDefFoundError");
	  addSignaturesClass("java.lang.ExceptionInInitializerError");
	  addSignaturesClass("java.lang.RuntimeException");
	  addSignaturesClass("java.lang.ClassNotFoundException");
	  addSignaturesClass("java.lang.ArithmeticException");
	  addSignaturesClass("java.lang.ArrayStoreException");
	  addSignaturesClass("java.lang.ClassCastException");
	  addSignaturesClass("java.lang.IllegalMonitorStateException");
	  addSignaturesClass("java.lang.IndexOutOfBoundsException");
	  addSignaturesClass("java.lang.ArrayIndexOutOfBoundsException");
	  addSignaturesClass("java.lang.NegativeArraySizeException");
	  addSignaturesClass("java.lang.NullPointerException");
	  addSignaturesClass("java.lang.InstantiationError");
	  addSignaturesClass("java.lang.InternalError");
	  addSignaturesClass("java.lang.OutOfMemoryError");
	  addSignaturesClass("java.lang.StackOverflowError");
	  addSignaturesClass("java.lang.UnknownError");
	  addSignaturesClass("java.lang.ThreadDeath");
	  addSignaturesClass("java.lang.ClassCircularityError");
	  addSignaturesClass("java.lang.ClassFormatError");
	  addSignaturesClass("java.lang.IllegalAccessError");
	  addSignaturesClass("java.lang.IncompatibleClassChangeError");
	  addSignaturesClass("java.lang.LinkageError");
	  addSignaturesClass("java.lang.VerifyError");
	  addSignaturesClass("java.lang.NoSuchFieldError");
	  addSignaturesClass("java.lang.AbstractMethodError");
	  addSignaturesClass("java.lang.NoSuchMethodError");
	  addSignaturesClass("java.lang.UnsatisfiedLinkError");

	  addSignaturesClass("java.lang.Thread");
	  addSignaturesClass("java.lang.Runnable");
	  addSignaturesClass("java.lang.Cloneable");

	  addSignaturesClass("java.io.Serializable");	

	  addSignaturesClass("java.lang.ref.Finalizer");
  }

  public void loadNecessaryClasses(){
    m_sourcePaths = SourceLocator.v().sourcePath();
    m_classPaths = SourceLocator.v().classPath();

    loadHierarchySootClasses();
    findEntryPoints();
    buildClassHierarchy();
    
    int prev_size = -1;
    while(prev_size != m_newInvokes.size()){
      prev_size = m_newInvokes.size();
      System.out.println("new_invokes: ");
      for(String new_invoke : m_newInvokes){
        System.out.println("  "+new_invoke);
      }
      for(String entry : m_entryPoints){
        System.out.println("entry point: "+entry);
        DfsInfo dfs_info = new DfsInfo(entry);
        m_dfsInfos.put(entry, dfs_info);
        m_currDfsInfo = dfs_info;

        loadStringCallGraph();
      }
    }


    //todo: use DfsValueSwitchCache
    //collectFields();

    //todo: look at these closely
    //cloneLibraryClasses();
    //remapFields();
    //remapTypes();

    //todo: write this. patch StringCallGraph and ClassHierarchy
    //patchState();
    
    m_classHierarchy.buildArrayTypes();
    m_classHierarchy.numberTypes();
    loadScene();

    for(String entry : m_entryPoints){
      m_currDfsInfo = m_dfsInfos.get(entry);
      dfsForRootbeer();
      m_currDfsInfo.expandArrayTypes();
      m_currDfsInfo.finalizeTypes();
    }

    Scene.v().loadDynamicClasses();
  }
 
  public void setLoaded(){
    m_loaded = true;
  }

  private void loadStringCallGraph(){
    String entry = m_currDfsInfo.getRootMethodSignature();

    System.out.println("loading forward string call graph for: "+entry+"...");
    m_cgVisitedMethods.clear();
    m_cgMethodQueue.add(entry);
    m_cgVisitedMethods.add(entry);

    m_currDfsInfo.getStringCallGraph().addEntryPoint(entry);

    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(entry);
    HierarchySootClass entry_class = m_classHierarchy.getHierarchySootClass(util.getClassName());
    HierarchySootMethod entry_ctor = entry_class.findMethodBySubSignature("void <init>()");
    m_cgMethodQueue.add(entry_ctor.getSignature());
    m_cgVisitedMethods.add(entry_ctor.getSignature());
    m_newInvokes.add(util.getClassName());

    for(String follow_signature : m_followSignatures){
      m_cgMethodQueue.add(follow_signature);
      m_cgVisitedMethods.add(follow_signature);
    }

    for(String follow_class : m_followClasses){
      HierarchySootClass follow_hclass = m_classHierarchy.getHierarchySootClass(follow_class);
      List<HierarchySootMethod> follow_methods = follow_hclass.getMethods();
      for(HierarchySootMethod follow_method : follow_methods){
        m_cgMethodQueue.add(follow_method.getSignature());
        m_cgVisitedMethods.add(follow_method.getSignature());
      }
    }

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
          String signature = method.getSignature();

          if(dontFollow(signature)){
            continue;
          }

          reverseStringGraphVisit(signature, reachable);   
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

      //System.out.println("processForwardStringCallGraphQueue: "+bfs_entry);
      m_currDfsInfo.getStringCallGraph().addSignature(bfs_entry);

      //add virtual methods to queue
      List<String> virt_methods = m_classHierarchy.getVirtualMethods(bfs_entry);
      for(String signature : virt_methods){
        if(dontFollow(signature)){
          continue;
        }

        if(m_cgVisitedMethods.contains(signature)){
          continue;
        }
        m_cgVisitedMethods.add(signature);
        //System.out.println("loadStringGraph adding virtual_method to queue: "+signature);
        m_cgMethodQueue.add(signature);
      }

      if(hmethod.isConcrete() == false){
        continue;
      }

      //add bfs methods to queue
      HierarchyValueSwitch value_switch = getValueSwitch(bfs_entry);
      m_newInvokes.addAll(value_switch.getNewInvokes());
  
      //System.out.println("new_invokes for: "+bfs_entry);
      //for(String new_invoke : value_switch.getNewInvokes()){
      //  System.out.println("  "+new_invoke);
      //}

      for(String dest_sig : value_switch.getMethodRefs()){
        if(dontFollow(dest_sig)){
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

      for(String array_type : value_switch.getArrayTypes()){
        m_classHierarchy.addArrayType(array_type);
      }

      //add <clinit> of class_refs
      /*
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
      */

      if(m_cgVisitedClasses.contains(class_name)){
        continue;
      }
      m_cgVisitedClasses.add(class_name);

      //add <clinit> to queue
      List<HierarchySootMethod> methods = hclass.getMethods();
      for(HierarchySootMethod method : methods){
        String name = method.getName();
        if(name.equals("<clinit>") && false){
          //System.out.println("loadStringGraph adding ctor: "+method.getSignature());
          if(dontFollow(method.getSignature())){
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
    //System.out.println("reverseStringGraphVisit: "+method_sig);
    MethodSignatureUtil util = new MethodSignatureUtil();
    HierarchyValueSwitch value_switch = getValueSwitch(method_sig);
    for(String dest_sig : value_switch.getMethodRefs()){
      if(dontFollow(dest_sig)){
        continue;
      }
      if(reachable.contains(dest_sig)){
        //System.out.println("loadStringGraph addEdge: "+method_sig+"->"+dest_sig);
        m_currDfsInfo.getStringCallGraph().addEdge(method_sig, dest_sig);
        reachable.add(method_sig);        

        //add to forward dfs
        if(dontFollow(method_sig) == false){
          if(m_cgVisitedMethods.contains(method_sig) == false){
            m_cgVisitedMethods.add(method_sig);
            //System.out.println("loadStringGraph adding virtual_method to queue: "+method_sig);
            m_cgMethodQueue.add(method_sig);
          }
        }

        //add virtual methods to queue
        List<String> virt_methods = m_classHierarchy.getVirtualMethods(method_sig);
        for(String virt_method : virt_methods){
          if(reachable.contains(virt_method) == false){
            reachable.add(virt_method);      

            if(dontFollow(virt_method)){
              continue;
            }
            reverseStringGraphVisit(virt_method, reachable);
          }
        }

        //add <clinit> to reachable
        util.parse(method_sig);
        String class_name = util.getClassName();
        HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
        List<HierarchySootMethod> methods = hclass.getMethods();
        for(HierarchySootMethod method : methods){
          if(dontFollow(method.getSignature())){
            continue;
          } 
          if(m_cgVisitedMethods.contains(method.getSignature())){
            continue;
          }
          m_cgVisitedMethods.add(method.getSignature());
          //m_cgMethodQueue.add(method.getSignature());

          String name = method.getName();
          if(name.equals("<clinit>") && false){
            //System.out.println("loadStringGraph adding ctor: "+method.getSignature());
            reachable.add(method.getSignature());          
          }
        }
      } 
    }

    //add <clinit> of class_refs
    /*
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
    */
    processForwardStringCallGraphQueue();
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


  private boolean dontFollow(String signature){
    if(m_dontDfsMethods.contains(signature)){
      return true;
    }
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);
    String class_name = util.getClassName();
    return ignorePackage(class_name);
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

      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(type_string);
      SootClass empty_class = new SootClass(type_string, hclass.getModifiers());
      Scene.v().addClass(empty_class);
      if(hclass.isApplicationClass()){
        System.out.println("  is_application_class true: "+type_string);
        empty_class.setApplicationClass();
      } else {
        System.out.println("  is_application_class false: "+type_string);
        empty_class.setLibraryClass();
      }

      if(hclass.hasSuperClass()){
        SootClass superClass = Scene.v().getSootClass(hclass.getSuperClass());
        empty_class.setSuperclass(superClass);
      }
      for(String iface : hclass.getInterfaces()){
        SootClass ifaceClass = Scene.v().getSootClass(iface);
        empty_class.addInterface(ifaceClass);
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
        String field_name = util.getName();

        HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
        int field_modifiers = hclass.getFieldModifiers(field_name);

        SootClass declaring_class = Scene.v().getSootClass(class_name);
        Type field_type = string_to_type.convert(util.getType());
        SootField new_field = new SootField(field_name, field_type, field_modifiers);
        declaring_class.addField(new_field);
      }
    }

    //add empty methods
    System.out.println("adding empty methods...");
    Set<String> to_signatures = new HashSet<String>();
    for(String signature_class : m_signaturesClasses){
      HierarchySootClass signature_hclass = m_classHierarchy.getHierarchySootClass(signature_class);
      List<HierarchySootMethod> signature_methods = signature_hclass.getMethods();
      for(HierarchySootMethod signature_method : signature_methods){
        to_signatures.add(signature_method.getSignature());
      }
    }
    to_signatures.addAll(all_sigs);
    for(String signature : to_signatures){
      System.out.println("  sig: "+signature);
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);
      String class_name = util.getClassName();

      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
      HierarchySootMethod method = hclass.findMethodBySubSignature(util.getSubSignature());
      
      List<Type> parameterTypes = new ArrayList<Type>();
      for(String paramType : method.getParameterTypes()){
        parameterTypes.add(string_to_type.convert(paramType));
      }
      Type returnType = string_to_type.convert(method.getReturnType());
      int modifiers = method.getModifiers();
      List<SootClass> thrownExceptions = new ArrayList<SootClass>();
      for(String exception : method.getExceptionTypes()){
        SootClass ex_class = Scene.v().getSootClass(exception);
        thrownExceptions.add(ex_class);
      }
      SootMethod soot_method = new SootMethod(method.getName(), parameterTypes,
        returnType, modifiers, thrownExceptions);

      SootClass soot_class = Scene.v().getSootClass(class_name);
      soot_class.addMethod(soot_method);
    }

    System.out.println("adding method bodies...");
    //add method bodies
    for(String signature : all_sigs){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);
      String class_name = util.getClassName();

      HierarchySootClass hclass = m_classHierarchy.getHierarchySootClass(class_name);
      HierarchySootMethod method = hclass.findMethodBySubSignature(util.getSubSignature());

      if(method.isConcrete() == false){
        continue;
      }

      SootClass soot_class = Scene.v().getSootClass(class_name);
      SootMethod soot_method = soot_class.getMethod(method.getSubSignature());

      System.out.println("  method.getBody: "+soot_method.getSignature());
      Body body = method.getBody(soot_method, "jb");
      soot_method.setActiveBody(body);
    }
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

  public Set<String> getNewInvokes(){
    return m_newInvokes;
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

  private void dfsForRootbeer(){
    String signature = m_currDfsInfo.getRootMethodSignature();
    
    Set<String> visited = new HashSet<String>();
    System.out.println("doing rootbeer dfs: "+signature);
    List<String> queue = new LinkedList<String>();
    queue.add(signature);

    for(ConditionalCudaEntry conditional_entry : m_conditionalCudaEntries){
      if(conditional_entry.condition(m_currDfsInfo)){
        queue.add(conditional_entry.getSignature());
      }
    }

    while(queue.isEmpty() == false){
      String curr = queue.get(0);
      queue.remove(0);
      doDfsForRootbeer(curr, queue, visited);
    }

    //for(String cuda_field : m_cudaFields){
    //  FieldSignatureUtil futil = new FieldSignatureUtil();
    //  futil.parse(cuda_field);
    //  
    //  SootField soot_field = futil.getSootField();
    //  m_currDfsInfo.addField(soot_field);
    //  m_currDfsInfo.addType(futil.getDeclaringClass());
    //}
  }

  private void doDfsForRootbeer(String signature, List<String> queue, Set<String> visited){
    HierarchyValueSwitch value_switch = getValueSwitch(signature);
    StringToType converter = new StringToType();
    FieldSignatureUtil futil = new FieldSignatureUtil();
    MethodSignatureUtil mutil = new MethodSignatureUtil();

    mutil.parse(signature);
    m_currDfsInfo.addType(mutil.getClassName());
    m_currDfsInfo.addType(mutil.getReturnType());
    m_currDfsInfo.addMethod(signature);

    for(String param_type : mutil.getParameterTypes()){
      m_currDfsInfo.addType(param_type);
    }

    for(String type_str : value_switch.getTypes()){
      Type type = converter.convert(type_str);
      m_currDfsInfo.addType(type);
    }    

    for(String type_str : value_switch.getArrayTypes()){
      ArrayType type = (ArrayType) converter.convert(type_str);
      m_currDfsInfo.addArrayType(type);
    }    

    for(String method_sig : value_switch.getMethodRefs()){
      if(dontFollow(method_sig)){
        continue;
      }
    
      if(visited.contains(method_sig) == false){
        queue.add(method_sig);
        visited.add(method_sig);
      }
    }

    for(String field_ref : value_switch.getFieldRefs()){
      futil.parse(field_ref);
      SootField soot_field = futil.getSootField();
      m_currDfsInfo.addField(soot_field);
    }

    for(String instanceof_str : value_switch.getInstanceOfs()){
      Type type = converter.convert(instanceof_str);
      m_currDfsInfo.addInstanceOf(type);
    }
  }

  public void applyOptimizations(){
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
        SootMethod curr_method = soot_class.getMethod(util.getSubSignature());
        if(curr_method.isConcrete()){
          Body body = curr_method.retrieveActiveBody();
          jop.apply(body);
        }
      }
    }
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
    Set<String> visited = new HashSet<String>();
    for(String jar : to_cache){
      if(jar.endsWith(".jar")){
        File file = new File(jar);
        if(file.exists() == false){
          continue;
        }
        if(visited.contains(jar)){
          continue;
        }
        visited.add(jar);
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
              //System.out.println("ignoring: "+entry.getName());
              continue;
            } 

            String name = entry.getName();
            String package_name;
            if(name.endsWith(".class")){
              String filename = name;
              name = name.replace(".class", "");
              name = name.replace("/", ".");
              package_name = getPackageName(name);

              boolean app_class = false;
              if(jar.equals(m_userJar)){
                app_class = true;
                m_appClasses.add(name);
              }
              HierarchySootClass hierarchy_class = hclassFactory.create(filename, jin);
              hierarchy_class.setApplicationClass(app_class);
              m_classHierarchy.put(name, hierarchy_class);

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

  private boolean shouldDfsMethod(SootMethod method){
    SootClass soot_class = method.getDeclaringClass();
    String pkg = soot_class.getPackageName();
    if(ignorePackage(pkg)){
      return false;
    } 
    return true;
  }

  private boolean ignorePackage(String class_name) {
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

  public void addSignaturesClass(String class_name){
    m_signaturesClasses.add(class_name);
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

  public DfsInfo getDfsInfo(){
    return m_currDfsInfo;
  }

}
