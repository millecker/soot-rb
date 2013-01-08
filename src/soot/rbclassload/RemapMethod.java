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

import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;
import soot.Local;
import soot.Type;
import soot.SootMethod;
import soot.SootClass;
import soot.Value;
import soot.ValueBox;
import soot.Body;
import soot.Unit;
import soot.RefType;
import soot.ArrayType;
import soot.SootClass;
import soot.SootField;
import soot.SootMethodRef;
import soot.util.NumberedString;
import soot.jimple.ParameterRef;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.CastExpr;
import soot.jimple.ThisRef;
import soot.options.Options;
import soot.Modifier;
import soot.Scene;

public class RemapMethod {

  private BuiltInRemaps m_remaps;

  public RemapMethod(){
    m_remaps = new BuiltInRemaps();
  }

  public void visit(SootMethod method) { 
    if(method.isConcrete() == false){
      return;
    } 
    Body body = method.retrieveActiveBody();
    if(body == null)
      return;
    
    fixArguments(method);
    Iterator<Unit> iter = body.getUnits().iterator();
    while(iter.hasNext()){
      Unit curr = iter.next();
      List<ValueBox> boxes = curr.getUseAndDefBoxes();
      for(ValueBox box : boxes){
        Value value = box.getValue();
        value = mutate(value);
        box.setValue(value);
      }
    }
  }

  private Value mutate(Value value) {
    if(value instanceof FieldRef){
      FieldRef ref = (FieldRef) value; 
      SootFieldRef field_ref = ref.getFieldRef();
      Type type = field_ref.getType();
      type = fixType(type);
      
      TypeToString converter = new TypeToString();
      String type_string = converter.toString(type);

      FieldSignatureUtil util = FieldSignatureUtil();
      util.parse(field_ref.getSignature());
      util.setType(type_string);

      SootField soot_field = util.getSootField();
      field_ref = soot_field.makeRef();
      ref.setFieldRef(field_ref);

      return reft;
    } else if(value instanceof InvokeExpr){
      InvokeExpr expr = (InvokeExpr) value;
      SootMethodRef ref = expr.getMethodRef();
      ref = remapRef(ref);
      expr.setMethodRef(ref);
    } else if(value instanceof NewExpr){
      NewExpr expr = (NewExpr) value;
      RefType base_type = expr.getBaseType();
      SootClass soot_class = base_type.getSootClass();
      if(shouldMap(soot_class)){
        SootClass new_class = getMapping(soot_class);
        expr.setBaseType(new_class.getType());
      }
      return value;
    } else if(value instanceof NewArrayExpr){
      NewArrayExpr expr = (NewArrayExpr) value;
      Type base_type = expr.getBaseType();
      base_type = fixType(base_type);
      expr.setBaseType(base_type);
      return value;      
    } else if(value instanceof NewMultiArrayExpr){
      NewMultiArrayExpr expr = (NewMultiArrayExpr) value;
      ArrayType array_type = expr.getBaseType();
      Type base_type = array_type.baseType;
      if(base_type instanceof RefType){
        RefType ref_type = (RefType) base_type;
        SootClass soot_class = ref_type.getSootClass();
        if(shouldMap(soot_class)){
          SootClass new_class = getMapping(soot_class);
          ArrayType new_type = ArrayType.v(new_class.getType(), array_type.numDimensions);
          expr.setBaseType(new_type);
        }
      }
      return value;
    } else if(value instanceof CastExpr){
      CastExpr expr = (CastExpr) value;
      Type cast_type = expr.getCastType();
      cast_type = fixType(cast_type);
      expr.setCastType(cast_type);
      return value;
    } else if(value instanceof ParameterRef){
      ParameterRef ref = (ParameterRef) value;
      Type new_type = fixType(ref.getType());
      return new ParameterRef(new_type, ref.getIndex());
    } else if(value instanceof ThisRef){
      ThisRef ref = (ThisRef) value;
      Type new_type = fixType(ref.getType());
      return new ThisRef((RefType) new_type);
    }else if(value instanceof Local){
      Local local = (Local) value;
      Type type = local.getType();
      local.setType(fixType(type));
      return value;
    } 
    return value;
  }

  private boolean shouldMap(SootClass soot_class) {
    if(Options.v().rbcl_remap_all() && soot_class.isLibraryClass()){
      return true;
    }
    if(m_remaps.containsKey(soot_class.getName())){
      return true;
    } else {
      return false;
    }
  }
 
  private void fixArguments(SootMethod method) {
    Type ret_type = method.getReturnType();
    method.setReturnType(fixType(ret_type));
    List param_types = method.getParameterTypes();
    List new_types = fixParameterList(param_types);
    method.setParameterTypes(new_types);    
  }
  
  private List fixParameterList(List param_types){
    List ret = new ArrayList();
    for(int i = 0; i < param_types.size(); ++i){
      Type type = (Type) param_types.get(i);
      ret.add(fixType(type));
    }  
    return ret;
  }
  
  private Type fixType(Type type){
    if(type instanceof RefType){
      RefType ref_type = (RefType) type;
      SootClass soot_class = ref_type.getSootClass();
      if(shouldMap(soot_class)){
        SootClass new_class = getMapping(soot_class);
        return new_class.getType();
      } else {
        return type;
      }
    } else if(type instanceof ArrayType){
      ArrayType array_type = (ArrayType) type;
      Type base = fixType(array_type.baseType);
      return ArrayType.v(base, array_type.numDimensions);
    } else {
      return type;
    }
  }
  
  private SootMethodRef remapRef(SootMethodRef ref) {
    Type return_type = fixType(ref.returnType());
    List params = fixParameterList(ref.parameterTypes());
    int modifiers = Modifier.PUBLIC;
    if(ref.isStatic()){
      modifiers += Modifier.STATIC;
    }
    SootMethod method = new SootMethod(ref.name(), params, return_type, modifiers);
    SootClass decl_class = ref.declaringClass();
    if(shouldMap(decl_class)){
      decl_class = getMapping(decl_class);
    }
    method.setDeclaringClass(decl_class);
    return method.makeRef();
  } 

  private SootClass getMapping(SootClass soot_class){
    String old_name = soot_class.getName();
    String new_name = Options.v().rbcl_remap_prefix() + old_name;
    return Scene.v().getSootClass(new_name);
  }
}
