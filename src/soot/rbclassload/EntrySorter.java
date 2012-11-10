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
import soot.SootMethod;
import soot.SootClass;
import java.util.Arrays;

public class EntrySorter {

  public void sort(List<SootMethod> entries){

    ToSort[] sorted = new ToSort[entries.size()];
    for(int i = 0; i < entries.size(); ++i){
      sorted[i] = new ToSort(entries.get(i));
    }
    Arrays.sort(sorted);

    entries.clear();
    for(ToSort to_sort : sorted){
      entries.add(to_sort.m_method);
    }
  }

  private class ToSort implements Comparable<ToSort> {
  
    public SootMethod m_method;
    private String m_className;
    private String m_methodName; 

    public ToSort(SootMethod method){
      m_method = method;

      SootClass soot_class = m_method.getDeclaringClass();
      m_className = soot_class.getName();

      m_methodName = method.getName();
    }

    public int compareTo(ToSort rhs){
      int ret = m_className.compareTo(rhs.m_className);
      if(ret != 0){
        return ret;
      }
      return m_methodName.compareTo(rhs.m_methodName);
    }
  }
}
