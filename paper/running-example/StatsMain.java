import com.javamex.classmexer.MemoryUtil;
import org.apache.commons.io.FileUtils;
import soot.*;

import java.util.Map;

public class StatsMain {

  private static class StatsTransformer extends SceneTransformer {
      private final String phase;

      public StatsTransformer(final String phase){
          this.phase = phase;
      }

      @Override
      protected void internalTransform(String phaseName, Map options) {
          long memoryUsed = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
          long memoryUsedClasses = MemoryUtil.deepMemoryUsageOfAll(Scene.v().getClasses(), MemoryUtil.VisibilityFilter.ALL);
          long memoryUsedScene = MemoryUtil.deepMemoryUsageOf(Scene.v(), MemoryUtil.VisibilityFilter.ALL);

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
          G.v().out.println("Memory used in "+phase+" phase: " + memoryUsed / (float) FileUtils.ONE_MB + " Mb\tMemory used for SootClass objects: "
                  + memoryUsedClasses / (float)FileUtils.ONE_MB + " Mb Scene size: " + memoryUsedScene/ (float)FileUtils.ONE_MB +" Mb");

      }
  }

  public static void main(String[] args){

    PackManager.v().getPack("wjpp").add(new Transform("wjpp.stats", new StatsTransformer("wjpp")));
    PackManager.v().getPack("wjtp").add(new Transform("wjtp.stats", new StatsTransformer("wjtp")));

    soot.Main.main(new String[]{
           "-time", "-w","-prepend-classpath", "-output-format", "none", "-soot-classpath", args[0], "-main-class", "A", "A"
    });
  }
}
