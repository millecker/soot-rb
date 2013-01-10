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

public class RootbeerClassLoader {

  private Map<String, DfsInfo> m_dfsInfos;
  private DfsInfo m_currDfsInfo;

  private Map<String, Set<String>> m_packageNameCache;
  private List<String> m_sourcePaths;
  private Map<String, String> m_classToFilename;
  private String m_tempFolder;
  private List<String> m_classPaths;
  private int m_loadedCount;
  private List<EntryPointDetector> m_entryDetectors;
  private List<String> m_ignorePackages;
  private List<String> m_keepPackages;
  private List<String> m_runtimeClasses;
  private List<String> m_appClasses;
  private List<String> m_entryPoints;
  private Set<String> m_visited;
  private String m_userJar;
  private StringCallGraph m_stringCG;
  private Set<String> m_reachableFields;
  private Map<String, String> m_remapping;
  private RemapClassName m_remapClassName;
  private boolean m_loaded;

  public RootbeerClassLoader(Singletons.Global g){
    m_dfsInfos = new HashMap<String, DfsInfo>();
    m_packageNameCache = new HashMap<String, Set<String>>();
    m_classToFilename = new HashMap<String, String>();
    m_entryDetectors = new ArrayList<EntryPointDetector>();

    String home = System.getProperty("user.home");
    File soot_folder = new File(home + File.separator + ".soot" + File.separator + "rbcl_cache");
    soot_folder.mkdirs();
    m_tempFolder = soot_folder.getAbsolutePath() + File.separator;
    m_loadedCount = 0;

    m_ignorePackages = new ArrayList<String>();    
    m_keepPackages = new ArrayList<String>();    
    m_runtimeClasses = new ArrayList<String>();

    m_appClasses = new ArrayList<String>();
    m_userJar = null;

    m_stringCG = new StringCallGraph();
    m_remapClassName = new RemapClassName();

    m_loaded = false;
  }

  public static RootbeerClassLoader v() { 
    return G.v().soot_rbclassload_RootbeerClassLoader(); 
  }

  public StringCallGraph getStringCallGraph(){
    return m_stringCG;
  }

  public List<String> getAllAppClasses(){
    return m_appClasses;
  }

  public void setUserJar(String filename){
    m_userJar = filename;
  }

  public void loadNecessaryClasses(){
    m_sourcePaths = SourceLocator.v().sourcePath();
    m_classPaths = SourceLocator.v().classPath();

    cachePackageNames();
    loadBuiltIns();
    loadToSignatures();
    sortApplicationClasses();
    findEntryPoints();
    loadForwardStringCallGraph();
    loadReverseStringCallGraph();
    segmentLibraryClasses();
    collectFields();
    cloneLibraryClasses();
    remapFields();
    remapTypes();
    dfsForRootbeer();

    Scene.v().loadDynamicClasses();
  }

  public List<String> getClassesToOutput(){
    List<String> ret = new ArrayList<String>();

    Set<String> ret_set = new HashSet<String>();
    Set<String> main_classes = new HashSet<String>();
    
    //collect class names from reachable method signatures
    Set<String> all_method_sigs = m_stringCG.getAllSignatures();
    System.out.println("reachable sigs: ");
    for(String sig : all_method_sigs){
      System.out.println("  "+sig);
    }
    System.exit(0);

    for(String method_sig : all_method_sigs){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(method_sig);
      util.remap();
      String class_name = util.getClassName();
      if(ret_set.contains(class_name) == false){
        ret_set.add(class_name);
      }
      String subsig = util.getMethodSubSignature();
      if(subsig.equals("void main(java.lang.String[])")){
        if(main_classes.contains(class_name) == false){
          main_classes.add(class_name);
        }
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

    //find <init> and <clinit> of main classes and don't delete them
    for(String main_class : main_classes){
      SootClass soot_class = Scene.v().getSootClass(main_class);
      if(soot_class.declaresMethod("void <init>()")){
        SootMethod init_method = soot_class.getMethod("void <init>()");
        String init_sig = init_method.getSignature();
        if(all_method_sigs.contains(init_sig) == false){
          all_method_sigs.add(init_sig);
        }
      }
      if(soot_class.declaresMethod("void <clinit>()")){
        SootMethod clinit_method = soot_class.getMethod("void <clinit>()");
        String clinit_sig = clinit_method.getSignature();
        if(all_method_sigs.contains(clinit_sig) == false){
          all_method_sigs.add(clinit_sig);
        }
      }
    }

    //trim things in classes that are not reachable
    for(String class_name : ret){
      SootClass soot_class = Scene.v().getSootClass(class_name);
      List<SootMethod> methods = soot_class.getMethods();
      List<SootMethod> methods_to_delete = new ArrayList<SootMethod>();
      for(SootMethod method : methods){
        String method_sig = method.getSignature();
        if(all_method_sigs.contains(method_sig) == false){
          methods_to_delete.add(method);
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

    return ret;
  }

  public void setLoaded(){
    m_loaded = true;
  }

  private void loadForwardStringCallGraph(){
    m_visited = new HashSet<String>();
    for(String entry : m_entryPoints){
      m_stringCG.addEntryPoint(entry);
      dfs(entry);     
    }
  }

  public boolean isLoaded(){
    return m_loaded;
  }

  private void dfs(String signature){
    if(m_visited.contains(signature)){
      return;
    }
    m_visited.add(signature);

    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);

    SootMethod method = util.getSootMethod();

    if(method.isConcrete() == false){
      return;
    }

    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

    Set<DfsMethodRef> methods = value_switch.getMethodRefs();
    for(DfsMethodRef ref : methods){
      SootMethodRef mref = ref.getSootMethodRef();
      String dest_sig = mref.getSignature();
      m_stringCG.addEdge(signature, dest_sig);
      dfs(dest_sig);
    }    
  }

  private void loadReverseStringCallGraph(){
    Set<String> reachable = new HashSet<String>();    
    reachable.addAll(m_entryPoints);
    int prev_size = -1;
    while(reachable.size() != prev_size){
      prev_size = reachable.size();
      for(String app_class : m_appClasses){
        SootClass soot_class = Scene.v().getSootClass(app_class);
        List<SootMethod> methods = soot_class.getMethods();
        for(SootMethod method : methods){
          reverseDfs(method, reachable);
        }
      }
    }
  }

  private void reverseDfs(SootMethod method, Set<String> reachable){
    String signature = method.getSignature();
    if(method.isConcrete() == false){
      return;
    }

    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

    Set<DfsMethodRef> methods = value_switch.getMethodRefs();
    for(DfsMethodRef ref : methods){
      SootMethodRef mref = ref.getSootMethodRef();
      String dest_sig = mref.getSignature();
      if(reachable.contains(dest_sig)){
        m_stringCG.addEdge(signature, dest_sig);
        reachable.add(signature);
      }
    }
  }

  private void sortApplicationClasses(){
    java.util.Collections.sort(m_appClasses);
  }

  private void segmentLibraryClasses(){
    for(String app_class : m_appClasses){
      m_stringCG.setApplicationClass(app_class);
    }

    Iterator<SootClass> iter = Scene.v().getClasses().iterator();
    while(iter.hasNext()){
      SootClass curr = iter.next();
      String name = curr.getName();
      if(m_appClasses.contains(name) == false){
        m_stringCG.setLibraryClass(name);
      }
    }        
  }

  private void collectFields(){
    m_reachableFields = new HashSet<String>();
    Set<String> all = m_stringCG.getAllSignatures();
    for(String sig : all){
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
  }

  private void cloneLibraryClasses(){
    m_remapping = new HashMap<String, String>();

    BuiltInRemaps built_in = new BuiltInRemaps();

    Set<String> lib_classes = m_stringCG.getLibraryClasses();
    String prefix = Options.v().rbcl_remap_prefix();

    for(String lib_class : lib_classes){
      if(built_in.containsKey(lib_class)){
        m_remapping.put(lib_class, built_in.get(lib_class));
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
    Set<String> lib_classes = m_stringCG.getLibraryClasses();
    BuiltInRemaps built_ins = new BuiltInRemaps();

    for(String field_sig : m_reachableFields){
      FieldSignatureUtil util = new FieldSignatureUtil();
      util.parse(field_sig);

      String declaring_class = util.getDeclaringClass();
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
    class_name = m_remapClassName.getMapping(class_name);
    util.setClassName(class_name);        

    return util.getSignature();
  }

  private void remapTypes(){    
    Iterator<SootClass> iter = Scene.v().getClasses().snapshotIterator();
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

    Set<String> all = m_stringCG.getAllSignatures();
    for(String signature : all){
      signature = remapClassOfMethodSignature(signature);      
      
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);

      SootMethod soot_method = util.getSootMethod();

      RemapMethod remapper = new RemapMethod();
      remapper.fixArguments(soot_method);
    }

    for(String signature : all){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(signature);
      util.remap();

      SootMethod soot_method = util.getSootMethod();

      RemapMethod remapper = new RemapMethod();
      remapper.visit(soot_method);
    }
  }

  private void dfsForRootbeer(){
    System.out.println("entry_points: ");
    for(String entry : m_entryPoints){
      System.out.println("  "+entry);
    }
    for(String entry : m_entryPoints){
      MethodSignatureUtil util = new MethodSignatureUtil();
      util.parse(entry);
      util.remap();

      SootMethod soot_method = util.getSootMethod();
      if(soot_method.getName().equals("gpuMethod") == false){
        continue;
      }

      DfsInfo dfs_info = new DfsInfo(soot_method);
      m_currDfsInfo = dfs_info;
      m_dfsInfos.put(soot_method.getSignature(), dfs_info);

      Set<String> visited = new HashSet<String>();
      System.out.println("doing rootbeer dfs: "+soot_method.getSignature());
      doDfs(soot_method, visited);     

      System.out.println("building class hierarchy for: "+entry+"...");
      m_currDfsInfo.expandArrayTypes();
      m_currDfsInfo.orderTypes();
      m_currDfsInfo.createClassHierarchy();
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
        SootMethod curr_method = soot_class.getMethod(util.getMethodSubSignature());
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

  private void cachePackageNames(){
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
          JarInputStream jin = new JarInputStream(new FileInputStream(jar));
          while(true){
            JarEntry entry = jin.getNextJarEntry();
            if(entry == null){
              break;
            }
            String name = entry.getName();
            if(name.endsWith(".class")){
              name = name.replace(".class", "");
              name = name.replace("/", ".");
              name = getPackageName(name);
            } else {
              name = name.replace("/", ".");
              name = name.substring(0, name.length()-1);
            }
            if(m_packageNameCache.containsKey(name)){
              Set<String> jars = m_packageNameCache.get(name);
              if(jars.contains(jar) == false){
                jars.add(jar);
              }
            } else {
              Set<String> jars = new HashSet<String>();
              jars.add(jar);
              m_packageNameCache.put(name, jars);
            }
          }
          jin.close();
        } catch(Exception ex){
          ex.printStackTrace();
        }
      }
    }
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

  private void addBasicMethod(String signature){
    MethodSignatureUtil util = new MethodSignatureUtil();
    util.parse(signature);

    String cls = util.getClassName();
    SootResolver.v().resolveClass(cls, SootClass.HIERARCHY);

    String method_sub_sig = util.getMethodSubSignature();
    SootClass soot_class = Scene.v().getSootClass(cls);

    SootMethod method = RootbeerClassLoader.v().findMethod(soot_class, method_sub_sig);
    SootResolver.v().resolveMethod(method);
  }

  private void addBasicClass(String class_name) {
    addBasicClass(class_name, SootClass.HIERARCHY);
  }

  private void addBasicClass(String class_name, int level) {
    resolveClass(class_name, level);
  }

  public void resolveClass(String class_name, int level){
    //TODO: figure this out for builtins
    //m_currDfsInfo.addType(RefType.v(class_name));
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

  private void loadToSignatures(){ 
    for(String src_folder : m_sourcePaths){
      File file = new File(src_folder);
      if(file.exists()){
        loadToSignatures(file, file);
      } else {
        System.out.println("file: "+src_folder+" does not exist!");
      }
    }
  }

  private void loadToSignatures(File curr, File src_file){
    File[] children = curr.listFiles();
    for(File child : children){
      if(child.isDirectory()){
        loadToSignatures(child, src_file);
      } else {
        String name = child.getName();
        if(name.startsWith(".") || name.endsWith(".class") == false){
          continue;
        }

        String full_name = child.getAbsolutePath();
        String input_folder = src_file.getAbsolutePath() + File.separator;
        String class_name = full_name.substring(input_folder.length());
        class_name = class_name.replace(File.separator, ".");
        class_name = class_name.substring(0, class_name.length() - ".class".length());

        if(ignorePackage(class_name)){
          continue;
        } 

        m_classToFilename.put(class_name, full_name);

        SootClass soot_class = SootResolver.v().resolveClass(class_name, SootClass.HIERARCHY);
        soot_class.setApplicationClass();        

        m_appClasses.add(soot_class.getName());
      }
    }
  }

  private void findEntryPoints(){
    m_entryPoints = new ArrayList<String>();
    for(String app_class : m_appClasses){
      SootClass curr = Scene.v().getSootClass(app_class);
      for(SootMethod method : curr.getMethods()){
        for(EntryPointDetector detector : m_entryDetectors){
          if(detector.isEntryPoint(method)){
            m_entryPoints.add(method.getSignature());
          }
        }
      }
    }
  }

  private void doDfs(SootMethod method, Set<String> visited){
    String signature = method.getSignature();
    if(visited.contains(signature)){
      return;
    }
    visited.add(signature);
    
    SootClass soot_class = method.getDeclaringClass();
    if(ignorePackage(soot_class.getName())){
      return;
    }

    m_currDfsInfo.addMethod(signature);
    m_currDfsInfo.addType(soot_class.getType());
    
    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

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

      if(dest.isConcrete() == false){
        continue;
      } 
      
      doDfs(dest, visited);
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
        
      m_currDfsInfo.addType(curr);
      
      SootClass type_class = findTypeClass(curr);
      if(type_class == null){
        continue;
      }
      
      type_class = SootResolver.v().resolveClass(type_class.getName(), SootClass.HIERARCHY);
      
      if(type_class.hasSuperclass()){
        queue.add(type_class.getSuperclass().getType());
        
        m_currDfsInfo.addSuperClass(curr, type_class.getSuperclass().getType());
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

  private void buildHierarchy(){
    System.out.println("building class hierarchy...");
    m_currDfsInfo.expandArrayTypes();
    m_currDfsInfo.orderTypes();
    m_currDfsInfo.createClassHierarchy(); 
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
