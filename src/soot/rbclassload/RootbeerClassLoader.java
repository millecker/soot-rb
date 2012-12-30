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
  private String m_userJar;

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
  }

  public static RootbeerClassLoader v() { 
    return G.v().soot_rbclassload_RootbeerClassLoader(); 
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
    
    System.out.println("source_paths: ");
    for(String path : m_sourcePaths){
      System.out.println(path);
    }
    cachePackageNames();
    loadBuiltIns();
    loadToSignatures();
    
    List<SootMethod> entries = findEntryPoints();
    EntrySorter sorter = new EntrySorter();
    sorter.sort(entries);

    Scene.v().setEntryPoints(entries);

    for(SootMethod entry : entries){
      m_currDfsInfo = new DfsInfo(entry);
      m_dfsInfos.put(entry.getSignature(), m_currDfsInfo);
      doDfs(entry);
      List<SootMethod> others = m_currDfsInfo.getOtherEntryPoints();
      for(SootMethod other : others){
        doDfs(other);
      }
      buildFullCallGraph(entry);
      System.out.println("fixing application classes...");
      fixApplicationClasses();
      buildHierarchy();
    }

    Scene.v().loadDynamicClasses();

    System.out.println("loaded "+m_loadedCount+" classes");
  }

  public void remapClasses(){
    System.out.println("remapping classes...");

    ClassRemapping remapping = new ClassRemapping();
    Collection<String> values = remapping.getValues();

    for(String value : values){
      resolveClass(value, SootClass.SIGNATURES);
    }

    List<SootMethod> entries = Scene.v().getEntryPoints();
    for(SootMethod entry : entries){
      String sig = entry.getSignature();
      m_currDfsInfo = m_dfsInfos.get(sig);
      DfsInfo info = getDfsInfo();

      List<String> sigs = info.getReachableMethodSigs();
      ClassRemappingTransform transform = new ClassRemappingTransform();
      transform.run(sigs);
      transform.finishClone();  

      Set<String> modified = transform.getModifiedClasses();
      for(String mod : modified){
        SootClass soot_class = Scene.v().getSootClass(mod);
        Scene.v().addRemappedClass(soot_class);
      }
             
      m_currDfsInfo = new DfsInfo(entry);
      m_dfsInfos.put(entry.getSignature(), m_currDfsInfo);
      doDfs(entry);
      List<SootMethod> others = m_currDfsInfo.getOtherEntryPoints();
      for(SootMethod other : others){
        doDfs(other);
      }
      m_currDfsInfo.loadBuiltInMethods();
      buildFullCallGraph(entry);
      System.out.println("fixing application classes...");
      fixApplicationClasses();
      buildHierarchy();
    }
  }

  public void applyOptimizations(){
    List<SootMethod> entries = Scene.v().getEntryPoints();
    Pack jop = PackManager.v().getPack("jop");
    
    for(SootMethod entry : entries){
      String entry_sig = entry.getSignature();
      m_currDfsInfo = m_dfsInfos.get(entry_sig);

      Set<String> methods = m_currDfsInfo.getMethods();
      for(String curr_sig : methods){
        MethodSignatureUtil util = new MethodSignatureUtil(curr_sig);
        SootClass soot_class = Scene.v().getSootClass(util.getClassName());
        SootMethod soot_method = soot_class.getMethod(util.getMethodSubSignature());
        if(soot_method.isConcrete()){
          Body body = soot_method.retrieveActiveBody();
          jop.apply(body);
        }
      }
    }
  }

  private void fixApplicationClasses(){
    Set<Type> types = m_currDfsInfo.getDfsTypes();
    types.addAll(m_currDfsInfo.getBuiltInTypes());
    Set<String> reachables = new HashSet<String>();
    for(Type type : types){
      SootClass type_class = findTypeClass(type);
      if(type_class == null){
        continue;
      }
      resolveClass(type_class.getName(), SootClass.HIERARCHY);
      reachables.add(type_class.getName());
    }
    for(String cls : m_appClasses){
      SootClass curr = Scene.v().getSootClass(cls);
      if(reachables.contains(cls)){
        curr.setApplicationClass();
      } else {
        curr.setLibraryClass();
      }
    }
  }

  public void loadDfsInfo(SootMethod entry){
    String sig = entry.getSignature();
    m_currDfsInfo = m_dfsInfos.get(sig);
    fixApplicationClasses();
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

    addBasicMethod("<edu.syr.pcpratts.rootbeer.runtime.Serializer: void <init>(edu.syr.pcpratts.rootbeer.runtime.memory.Memory,edu.syr.pcpratts.rootbeer.runtime.memory.Memory)>");
    addBasicMethod("<edu.syr.pcpratts.rootbeer.runtime.Sentinal: void <init>()>");

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

  private List<SootMethod> findEntryPoints(){
    List<SootMethod> ret = new ArrayList<SootMethod>();
    Iterator<SootClass> iter = Scene.v().getApplicationClasses().iterator();
    while(iter.hasNext()){
      SootClass curr = iter.next();
      for(SootMethod method : curr.getMethods()){
        for(EntryPointDetector detector : m_entryDetectors){
          if(detector.isEntryPoint(method)){
            ret.add(method);
          }
        }
      }
    }
    return ret;
  }

  private void doDfs(SootMethod method){
    String signature = method.getSignature();
    if(m_currDfsInfo.containsMethod(signature)){
      return;
    }
    m_currDfsInfo.addMethod(signature);

    //System.out.println("doDfs: "+signature);
        
    SootClass soot_class = method.getDeclaringClass();
    addType(soot_class.getType());

    if(ignorePackage(soot_class.getName())){
      return;
    }
    
    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

    Set<SootFieldRef> fields = value_switch.getFieldRefs();
    for(SootFieldRef ref : fields){
      addType(ref.type());
      
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
      
      m_currDfsInfo.addCallGraphEdge(method, ref.getStmt(), dest);
      doDfs(dest);
    }
    
    while(soot_class.hasSuperclass()){
      SootClass super_class = soot_class.getSuperclass();
      if(super_class.declaresMethod(method.getSubSignature())){
        SootMethod super_method = super_class.getMethod(method.getSubSignature());
        doDfs(super_method);
      }
      soot_class = super_class;
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

      Iterator<SootField> iter = type_class.getFields().iterator();
      while(iter.hasNext()){
        SootField curr_field = iter.next();
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

  private void buildFullCallGraph(SootMethod method){
    System.out.println("building full call graph for: "+method.getDeclaringClass().getName()+"...");

    List<SootMethod> queue = new LinkedList<SootMethod>();
    Set<SootMethod> visited = new HashSet<SootMethod>();

    CallGraph call_graph = m_currDfsInfo.getCallGraph();

    SootClass soot_class = method.getDeclaringClass();
    for(SootMethod sibling_method : soot_class.getMethods()){
      if(sibling_method.getName().equals("<init>")){
        queue.add(sibling_method);
      } 
    }
    queue.add(method);

    Iterator<String> iter = m_appClasses.iterator();
    while(iter.hasNext()){

      SootClass curr_class = Scene.v().getSootClass(iter.next());

      for(SootMethod curr_method : curr_class.getMethods()){
      
        DfsValueSwitch value_switch = new DfsValueSwitch();
        value_switch.run(curr_method);
        
        Set<DfsMethodRef> method_refs = value_switch.getMethodRefs();
        for(DfsMethodRef dfs_ref : method_refs){
          m_currDfsInfo.addCallGraphEdge(curr_method, dfs_ref.getStmt(), dfs_ref.getSootMethodRef().resolve());
        }
      }
    }

    while(queue.isEmpty() == false){
      SootMethod curr = queue.get(0);
      queue.remove(0);

      m_currDfsInfo.addReachableMethodSig(curr.getSignature());

      //System.out.println("call graph dfs: "+curr.getSignature());

      DfsValueSwitch value_switch = new DfsValueSwitch();
      value_switch.run(curr);

      Set<Type> all = value_switch.getAllTypes();
      for(Type type : all){
        addType(type);
      }
      
      Iterator<Edge> curr_into = call_graph.edgesInto(curr);
      
      addToQueue(curr_into, queue, visited);
    }
  }

  private void addToQueue(Iterator<Edge> edges, List<SootMethod> queue, Set<SootMethod> visited){
    while(edges.hasNext()){
      Edge edge = edges.next();
      
      SootMethod src = edge.src();
      if(visited.contains(src) == false && shouldDfsMethod(src)){
        queue.add(src);
        visited.add(src);
      }
      
      SootMethod dest = edge.tgt();
      if(visited.contains(dest) == false && shouldDfsMethod(dest)){
        queue.add(dest);
        visited.add(dest);
      }
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
