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

import java.util.Iterator;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

public class MethodFinder {
  
  public SootMethod find(String method_sig){
    MethodSignatureUtil util = new MethodSignatureUtil(method_sig);
    String class_name = util.getClassName();
    String method_subsig = util.getMethodSubSignature();
    SootClass soot_class = Scene.v().getSootClass(class_name);
    if(soot_class.isPhantom()){
      return null;
    }
    SootClass curr_class = soot_class;
    while(true){
      SootMethod ret = find(curr_class, method_subsig);
      if(ret == null){
        Iterator<SootClass> iter = curr_class.getInterfaces().iterator();
        while(iter.hasNext()){
          SootClass curr = iter.next();
          ret = find(curr, method_subsig);
          if(ret != null){
            return ret;
          }
        }
        if(curr_class.hasSuperclass() == false){
          return null;
        }
        curr_class = curr_class.getSuperclass();
      } else {
        return ret;
      }
    }
  }

  private SootMethod find(SootClass soot_class, String method_subsig) {
    try {
      return soot_class.getMethod(method_subsig);
    } catch(Exception ex){
      return null;
    }
  }
}
