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

import java.util.List;
import java.util.ArrayList;
import java.io.InputStream;
import java.io.DataInputStream;
import java.io.IOException;

public class HierarchySootClass {

  private String m_className;
  private String m_superClassName;
  private List<String> m_interfaceNames;

  private int m_magic;
  private int m_minorVersion;
  private int m_majorVersion;
  private int constant_pool_count;
  private cp_info[] constant_pool;

  public HierarchySootClass(String name){
    m_className = name;
    m_interfaceNames = new ArrayList<String>();
  }

  public boolean readHierarchy(InputStream input_stream){
    DataInputStream data_stream = new DataInputStream(input_stream);
 
    try {
      m_magic = data_stream.readInt();
      m_minorVersion = data_stream.readUnsignedShort();
      m_majorVersion = data_stream.readUnsignedShort();

      constant_pool_count = data_stream.readUnsignedShort();

      if(!readConstantPool(data_stream)){
        return false;
      }

      //eat access_flags
      data_stream.readUnsignedShort();

      //eat this_class
      data_stream.readUnsignedShort();

      m_superClassName = getClassConstant(data_stream.readUnsignedShort());

      int interfaces_count = data_stream.readUnsignedShort();
      for(int i = 0; i < interfaces_count; ++i){
        m_interfaceNames.add(getClassConstant(data_stream.readUnsignedShort()));
      }
    } catch(IOException ex){
      ex.printStackTrace();
      return false;
    }

    return true;
  }

  private String getClassConstant(int index){
    cp_info entry = constant_pool[index];
    CONSTANT_Class_info class_info = (CONSTANT_Class_info) entry;
    int name_index = class_info.name_index;
    cp_info class_name = constant_pool[name_index];
    CONSTANT_Utf8_info utf8_info = (CONSTANT_Utf8_info) class_name;
    String converted_name = utf8_info.convert();
    String java_name = converted_name.replace("/", ".");
    return java_name;
  }

  /** Reads in the constant pool from the given stream.
    * @param d Stream forming the <tt>.class</tt> file.
    * @return <i>true</i> if read was successful, <i>false</i> on some error.
    * @exception java.io.IOException on error.
    */
   private boolean readConstantPool(DataInputStream d) throws IOException {
      byte tag;
      cp_info cp;
      int i;
      boolean skipone;   // set if next cp entry is to be skipped

      constant_pool = new cp_info[constant_pool_count];
      //Instruction.constant_pool = constant_pool;
      skipone = false;

      for (i=1;i<constant_pool_count;i++) {
         if (skipone) {
            skipone = false;
            continue;
         }
         tag = (byte)d.readUnsignedByte();
         switch(tag) {
         case cp_info.CONSTANT_Class:
            cp = new CONSTANT_Class_info();
            ((CONSTANT_Class_info)cp).name_index = d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_Fieldref:
            cp = new CONSTANT_Fieldref_info();
            ((CONSTANT_Fieldref_info)cp).class_index = d.readUnsignedShort();
            ((CONSTANT_Fieldref_info)cp).name_and_type_index =
                d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_Methodref:
            cp = new CONSTANT_Methodref_info();
            ((CONSTANT_Methodref_info)cp).class_index = d.readUnsignedShort();
            ((CONSTANT_Methodref_info)cp).name_and_type_index =
               d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_InterfaceMethodref:
            cp = new CONSTANT_InterfaceMethodref_info();
            ((CONSTANT_InterfaceMethodref_info)cp).class_index =
               d.readUnsignedShort();
            ((CONSTANT_InterfaceMethodref_info)cp).name_and_type_index =
               d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_String:
            cp = new CONSTANT_String_info();
            ((CONSTANT_String_info)cp).string_index =
                d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_Integer:
            cp = new CONSTANT_Integer_info();
            ((CONSTANT_Integer_info)cp).bytes = d.readInt();
            break;
         case cp_info.CONSTANT_Float:
            cp = new CONSTANT_Float_info();
            ((CONSTANT_Float_info)cp).bytes = d.readInt();
            break;
         case cp_info.CONSTANT_Long:
            cp = new CONSTANT_Long_info();
            ((CONSTANT_Long_info)cp).high = d.readInt() & 0xFFFFFFFFL;
            ((CONSTANT_Long_info)cp).low = d.readInt() & 0xFFFFFFFFL;
            skipone = true;  // next entry needs to be skipped
            break;
         case cp_info.CONSTANT_Double:
            cp = new CONSTANT_Double_info();
            ((CONSTANT_Double_info)cp).high = d.readInt() & 0xFFFFFFFFL;
            ((CONSTANT_Double_info)cp).low = d.readInt() & 0xFFFFFFFFL;
            skipone = true;  // next entry needs to be skipped
            break;
         case cp_info.CONSTANT_NameAndType:
            cp = new CONSTANT_NameAndType_info();
            ((CONSTANT_NameAndType_info)cp).name_index =
               d.readUnsignedShort();
            ((CONSTANT_NameAndType_info)cp).descriptor_index =
               d.readUnsignedShort();
            break;
         case cp_info.CONSTANT_Utf8:
            CONSTANT_Utf8_info cputf8 = new CONSTANT_Utf8_info(d);
            // If an equivalent CONSTANT_Utf8 already exists, we return
            // the pre-existing one and allow cputf8 to be GC'd.
            cp = (cp_info) CONSTANT_Utf8_collector.v().add(cputf8);
            break;
         case cp_info.CONSTANT_MethodHandle:
             cp = new CONSTANT_MethodHandle_info();
             ((CONSTANT_MethodHandle_info)cp).kind = d.readByte();
             ((CONSTANT_MethodHandle_info)cp).target_index = d.readUnsignedShort();
             break;
         case cp_info.CONSTANT_InvokeDynamic:
             cp = new CONSTANT_InvokeDynamic_info();
             ((CONSTANT_InvokeDynamic_info)cp).bootstrap_method_index = d.readUnsignedShort();
             ((CONSTANT_InvokeDynamic_info)cp).name_and_type_index = d.readUnsignedShort();
             break;
         default:
            return false;
         }
         cp.tag = tag;
         constant_pool[i] = cp;
      }
      return true;
   }
}
