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

import java.util.Map;
import java.util.HashMap;

public class BuiltInRemaps {

  private Map<String, String> m_mapping;

  public BuiltInRemaps(){
    m_mapping = new HashMap<String, String>();
    m_mapping.put("java.util.concurrent.atomic.AtomicLong", "edu.syr.pcpratts.rootbeer.runtime.remap.GpuAtomicLong");
    m_mapping.put("java.util.Random", "edu.syr.pcpratts.rootbeer.runtime.remap.Random");
    m_mapping.put("edu.syr.pcpratts.rootbeer.testcases.rootbeertest.remaptest.CallsPrivateMethod", "edu.syr.pcpratts.rootbeer.runtime.remap.DoesntCallPrivateMethod");
    m_mapping.put("java.lang.Math", "edu.syr.pcpratts.rootbeer.runtime.remap.java.lang.Math");
  }

  public boolean containsKey(String key){
    return m_mapping.containsKey(key);
  } 

  public String get(String key){
    return m_mapping.get(key);
  }
}
