
package edu.syr.pcpratts.rootbeer.classloaderanalysis;

import soot.options.Options;

public class RootbeerClassLoaderAnalysis {

  public void run(String folder){
    Options.v().set_rbclassload(true);
    
    String[] args = {
      "-pp",
      "-process-dir", "classes"
    };
    
    soot.Main.main(args);
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
