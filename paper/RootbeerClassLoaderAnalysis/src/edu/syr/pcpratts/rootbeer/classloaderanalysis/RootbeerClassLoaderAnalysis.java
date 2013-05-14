
package edu.syr.pcpratts.rootbeer.classloaderanalysis;

import soot.options.Options;
import java.util.List;
import java.util.ArrayList;
import soot.rbclassload.RootbeerClassLoader;

public class RootbeerClassLoaderAnalysis {

  public void run(String folder){
    
    List<String> proc_dir = new ArrayList<String>();
    proc_dir.add("classes/soap2013_example.jar");
    
    Options.v().set_rbclassload(true);
    Options.v().set_process_dir(proc_dir);
    Options.v().set_prepend_classpath(true);
    
    RootbeerClassLoader.v().setUserJar("classes/soap2013_example.jar");
    RootbeerClassLoader.v().addEntryMethodTester(new EntryPointDetector());
    RootbeerClassLoader.v().loadNecessaryClasses();
    
    System.out.println("done");
  }
  
  public static void main(String[] args) {
    RootbeerClassLoaderAnalysis analysis = new RootbeerClassLoaderAnalysis();
    analysis.run("classes/");
  }
}

/*
     List<String> proc_dir = new ArrayList<String>();
    proc_dir.add(RootbeerPaths.v().getJarContentsFolder());
    
    Options.v().set_allow_phantom_refs(true);
    Options.v().set_rbclassload(true);
    Options.v().set_prepend_classpath(true);
    Options.v().set_process_dir(proc_dir);
    Options.v().set_soot_classpath(rootbeer_jar);
    RootbeerClassLoader.v().addEntryMethodTester(m_entryDetector);
    RootbeerClassLoader.v().loadNecessaryClasses();
 */
