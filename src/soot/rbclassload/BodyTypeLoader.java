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
import soot.ArrayType;
import soot.SootResolver;
import soot.SootClass;
import soot.Trap;
import soot.jimple.FieldRef;
import soot.SootFieldRef;
import soot.SootMethodRef;
import soot.jimple.JimpleBody;
import soot.jimple.NewExpr;
import soot.jimple.InvokeExpr;
import soot.Scene;
import soot.Local;
import soot.UnitBox;
import soot.SootMethod;

import java.util.Iterator;
import java.util.List;

public class BodyTypeLoader {

  public void load(JimpleBody jb){
    SootMethod soot_method = jb.getMethod();
    loadClass(soot_method.getReturnType());
    List<Type> params = soot_method.getParameterTypes();
    for(Type param : params){
      loadClass(param);
    } 
    List<SootClass> exceptions = soot_method.getExceptions();
    for(SootClass exception : exceptions){
      loadClass(exception.getName());
    }

    Iterator<Unit> iter = jb.getUnits().iterator();
    while(iter.hasNext()){
      Unit curr = iter.next();
      handleUnit(curr);
    }

    Iterator<Trap> iter2 = jb.getTraps().iterator();
    while(iter2.hasNext()){
      Trap curr = iter2.next();
      SootClass except = curr.getException();
      loadClass(except.getName());
      
      List<UnitBox> boxes = curr.getUnitBoxes();
      for(UnitBox box : boxes){
        handleUnit(box.getUnit());
      }
    }   
  }

  private void handleUnit(Unit curr){
    List<ValueBox> values = curr.getUseAndDefBoxes();
    for(ValueBox box : values){ 
      Value value = box.getValue();

      //unknown types can be created with new
      if(value instanceof NewExpr){
        NewExpr expr = (NewExpr) value;
        RefType ref_type = expr.getBaseType();
        String class_name = ref_type.getClassName();
        loadClass(class_name);
      }

      if(value instanceof Local){
        Local local = (Local) value;
        Type type = local.getType();
        if(type instanceof RefType){
          RefType ref_type = (RefType) type;
          String class_name = ref_type.getClassName();
          loadClass(class_name);
        }
      }

      if(value instanceof FieldRef){
        FieldRef field_ref = (FieldRef) value;
        SootFieldRef soot_field_ref = field_ref.getFieldRef();
        loadClass(soot_field_ref.declaringClass().getName());
        loadClass(soot_field_ref.type());
      }
    }
  }

  private void loadClass(Type type){
    if(type instanceof RefType){
      RefType ref_type = (RefType) type;
      loadClass(ref_type.getClassName());
    } else if(type instanceof ArrayType){
      ArrayType array_type = (ArrayType) type;
      loadClass(array_type.baseType);
    }
  }

  private void loadClass(String name){
    RootbeerClassLoader.v().resolveClass(name, SootClass.HIERARCHY);
    SootClass soot_class = Scene.v().getSootClass(name);
    Iterator<SootClass> iter = soot_class.getInterfaces().iterator();
    while(iter.hasNext()){
      SootClass curr = iter.next();
      RootbeerClassLoader.v().resolveClass(curr.getName(), SootClass.HIERARCHY);
    }
  }
}
