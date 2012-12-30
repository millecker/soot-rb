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

import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.Type;
import soot.RefType;
import soot.SootResolver;
import soot.SootClass;
import soot.Trap;
import soot.SootMethodRef;
import soot.jimple.JimpleBody;
import soot.jimple.NewExpr;
import soot.jimple.InvokeExpr;

import java.util.Iterator;
import java.util.List;

public class BodyTypeLoader {

  public void load(JimpleBody jb){
    Iterator<Unit> iter = jb.getUnits().iterator();
    while(iter.hasNext()){
      Unit curr = iter.next();
      List<ValueBox> values = curr.getUseAndDefBoxes();
      for(ValueBox box : values){
        Value value = box.getValue();

        //unknown types can be created with new
        if(value instanceof NewExpr){
          NewExpr expr = (NewExpr) value;
          RefType ref_type = expr.getBaseType();
          String class_name = ref_type.getClassName();
          RootbeerClassLoader.v().resolveClass(class_name, SootClass.HIERARCHY);
        } 

      }
    }

    Iterator<Trap> iter2 = jb.getTraps().iterator();
    while(iter2.hasNext()){
      Trap curr = iter2.next();
      SootClass except = curr.getException();
      System.out.println("except: "+except.getName());
      RootbeerClassLoader.v().resolveClass(except.getName(), SootClass.HIERARCHY);
    }   
  }
}
