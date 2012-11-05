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

import soot.SootMethodRef;
import soot.jimple.Stmt;

public class DfsMethodRef {
  
  private final SootMethodRef m_ref;
  private final Stmt m_stmt;

  public DfsMethodRef(SootMethodRef ref, Stmt stmt){
    m_ref = ref;
    m_stmt = stmt;
  }
  
  public SootMethodRef getSootMethodRef(){
    return m_ref;
  }
  
  public Stmt getStmt(){
    return m_stmt;
  } 
  
  @Override
  public boolean equals(Object other){
    if(other instanceof DfsMethodRef == false){
      return false;
    }
    DfsMethodRef rhs = (DfsMethodRef) other;
    if(m_ref.equals(rhs.m_ref) && m_stmt.equals(rhs.m_stmt)){
      return true;
    }
    return false;
  }

  @Override
  public int hashCode() {
    int hash = 3;
    hash = 23 * hash + (this.m_ref != null ? this.m_ref.hashCode() : 0);
    hash = 23 * hash + (this.m_stmt != null ? this.m_stmt.hashCode() : 0);
    return hash;
  }
}
