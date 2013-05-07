import soot.*;

import java.util.Map;

public class StatsMain {

  public static void main(String[] args){

    PackManager.v().getPack("wjtp").add(new Transform("wjtp.stats", new SceneTransformer() {
      @Override
      protected void internalTransform(String phaseName, Map options) {
        int resolvedBodies =0, resolvedSignatures= 0 , resolvedHierarchy = 0, dandling = 0;
        int numMethods = 0;

        for (SootClass sc : Scene.v().getClasses()){
          if (sc.resolvingLevel() == SootClass.DANGLING){
            dandling ++;
          }
          else if (sc.resolvingLevel() == SootClass.HIERARCHY){
            resolvedHierarchy++;
          }
          else if (sc.resolvingLevel() == SootClass.SIGNATURES){
            resolvedSignatures++;
            numMethods += sc.getMethodCount();
          } else if (sc.resolvingLevel() == SootClass.BODIES){
            resolvedBodies++;
            numMethods += sc.getMethodCount();
          }
        }

        G.v().out.println("Dandling: " + dandling + " Hierarchy: " + resolvedHierarchy + " Signatures: " + resolvedSignatures + " Bodies: "+ resolvedBodies +". Num SootMethod: "+ numMethods);
      }
    }));

    soot.Main.main(new String[]{
            "-w","-prepend-classpath", "-output-format", "none", "-soot-classpath", args[0], "A"
    });
  }
}
