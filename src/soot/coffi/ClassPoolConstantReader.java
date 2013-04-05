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

package soot.coffi;

public class ClassPoolConstantReader {

  public String get(int index, cp_info[] constant_pool){
    cp_info entry = constant_pool[index];
    if(entry instanceof CONSTANT_Class_info){
      CONSTANT_Class_info class_info = (CONSTANT_Class_info) entry;
      int name_index = class_info.name_index;
      cp_info class_name = constant_pool[name_index];
      CONSTANT_Utf8_info utf8_info = (CONSTANT_Utf8_info) class_name;
      String converted_name = utf8_info.convert();
      String java_name = converted_name.replace("/", ".");
      return java_name;
    } else {
      throw new RuntimeException("unknown type: "+entry);
    }
  }

}
