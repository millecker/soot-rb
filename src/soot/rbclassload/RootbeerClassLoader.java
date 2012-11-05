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
import soot.jimple.Stmt;

import java.util.List;
import java.util.LinkedList;
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

  private Map<String, SubScene> m_subScenes;
  private SubScene m_currSubScene;

  private Map<String, Set<String>> m_packageNameCache;
  private List<String> m_sourcePaths;
  private Map<String, String> m_classToFilename;
  private String m_tempFolder;
  private List<String> m_classPaths;
  private int m_loadedCount;

  public RootbeerClassLoader(Singletons.Global g){
    m_subScenes = new HashMap<String, SubScene>();
    m_packageNameCache = new HashMap<String, Set<String>>();
    m_classToFilename = new HashMap<String, String>();
    m_tempFolder = "temp" + File.separator;
    m_loadedCount = 0;
  }

  public static RootbeerClassLoader v() { 
    return G.v().soot_rbclassload_RootbeerClassLoader(); 
  }

  public void loadNecessaryClasses(){
    m_currSubScene = new SubScene();

    m_sourcePaths = SourceLocator.v().sourcePath();
    m_classPaths = SourceLocator.v().classPath();
    
    System.out.println("source_paths: ");
    for(String path : m_sourcePaths){
      System.out.println(path);
    }
    cachePackageNames();
    loadBuiltIns();
    loadToSignatures();
    
    SootMethod entry = findEntryPoint();
    doDfs(entry);
    buildFullCallGraph(entry);
    findReachableMethods();
    buildHierarchy();

    Scene.v().loadDynamicClasses();
  }

  private void cachePackageNames(){
    List<String> paths = SourceLocator.v().classPath();
    String[] to_cache = new String[paths.size()];
    to_cache = paths.toArray(to_cache);
    Arrays.sort(to_cache);
    for(String jar : to_cache){
      if(jar.endsWith(".jar")){
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
	  addBasicClass("java.lang.Class", SootClass.SIGNATURES);

	  addBasicClass("java.lang.Void", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Boolean", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Byte", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Character", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Short", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Integer", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Long", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Float", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Double", SootClass.SIGNATURES);

	  addBasicClass("java.lang.String");
	  addBasicClass("java.lang.StringBuffer", SootClass.SIGNATURES);

	  addBasicClass("java.lang.Error");
	  addBasicClass("java.lang.AssertionError", SootClass.SIGNATURES);
	  addBasicClass("java.lang.Throwable", SootClass.SIGNATURES);
	  addBasicClass("java.lang.NoClassDefFoundError", SootClass.SIGNATURES);
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

    System.out.println("loading: "+class_name);

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

    if(m_classToFilename.containsKey(class_name) == false){
      return null;
    }

    try {
      String full_filename = m_classToFilename.get(class_name);
      InputStream stream = new FileInputStream(full_filename);
		  if(stream == null){
        return null;
      }
		  return new CoffiClassSource(class_name, stream);
    } catch(FileNotFoundException ex){
      return null;
    }
  }

  private void loadToSignatures(){ 
    System.out.println("loaded "+m_loadedCount+" classes");
    for(String src_folder : m_sourcePaths){
      File file = new File(src_folder);
      loadToSignatures(file, file);
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
        m_classToFilename.put(class_name, full_name);

        SootClass soot_class = SootResolver.v().resolveClass(class_name, SootClass.SIGNATURES);
        soot_class.setApplicationClass();        
      }
    }
  }

  private SootMethod findEntryPoint(){
    String main_subsig = "void main(java.lang.String[])";
    Iterator<SootClass> iter = Scene.v().getApplicationClasses().iterator();
    while(iter.hasNext()){
      SootClass curr = iter.next();
      for(SootMethod method : curr.getMethods()){
        if(method.getSubSignature().equals(main_subsig)){
          Scene.v().setMainClass(curr);
          return method;
        }
      }
    }
    return null;
  }

  private void doDfs(SootMethod method){
    String signature = method.getSignature();
    if(m_currSubScene.containsMethod(signature)){
      return;
    }
    m_currSubScene.addMethod(signature);
        
    SootClass soot_class = method.getDeclaringClass();
    addType(soot_class.getType());
    
    DfsValueSwitch value_switch = new DfsValueSwitch();
    value_switch.run(method);

    Set<SootFieldRef> fields = value_switch.getFieldRefs();
    for(SootFieldRef ref : fields){
      addType(ref.type());
      
      SootField field = ref.resolve();
      m_currSubScene.addField(field);
    }
    
    Set<Type> instance_ofs = value_switch.getInstanceOfs();
    for(Type type : instance_ofs){
      m_currSubScene.addInstanceOf(type);
    }

    Set<DfsMethodRef> methods = value_switch.getMethodRefs();
    for(DfsMethodRef ref : methods){
      SootMethodRef mref = ref.getSootMethodRef();
      SootClass method_class = mref.declaringClass();
      SootResolver.v().resolveClass(method_class.getName(), SootClass.BODIES);
      SootMethod dest = mref.resolve();

      if(dest.isConcrete() == false){
        continue;
      } 
      
      addType(method_class.getType());
      
      m_currSubScene.addCallGraphEdge(method, ref.getStmt(), dest);
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

  public void addType(Type type) {
    List<Type> queue = new LinkedList<Type>();
    queue.add(type);
    while(queue.isEmpty() == false){
      Type curr = queue.get(0);
      queue.remove(0);
      
      if(m_currSubScene.containsType(curr)){
        continue;
      }
        
      m_currSubScene.addType(curr);
      
      SootClass type_class = findTypeClass(curr);
      if(type_class == null){
        continue;
      }
      
      System.out.println("addType: "+type_class.getName());

      type_class = SootResolver.v().resolveClass(type_class.getName(), SootClass.SIGNATURES);
      
      if(type_class.hasSuperclass()){
        queue.add(type_class.getSuperclass().getType());
        
        m_currSubScene.addSuperClass(curr, type_class.getSuperclass().getType());
      }
      
      if(type_class.hasOuterClass()){
        queue.add(type_class.getOuterClass().getType());
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

  }

  private void findReachableMethods(){

  }

  private void buildHierarchy(){

  }

}
