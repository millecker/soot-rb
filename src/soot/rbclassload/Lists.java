/* 
 * Copyright 2012 Phil Pratt-Szeliga and other contributors
 * http://chirrup.org/
 * 
 * See the file LICENSE for copying permission.
 */

package soot.rbclassload;

import java.util.List;

public class Lists {
	
	interface Predicate<T> {
	    boolean apply(T item);
	}
	
	public static <T> int find(List<T> items, Predicate<T> predicate) {
	    for(int pos=0; pos<items.size(); pos++) {
	        if(predicate.apply(items.get(pos))) {
	            return pos;
	        }
	    }
	    return -1;
	}
	
	public static <T> int find(List<T> items, Predicate<T> predicate, int startPos) {
	    for(int pos=startPos; pos<items.size(); pos++) {
	        if(predicate.apply(items.get(pos))) {
	            return pos;
	        }
	    }
	    return -1;
	}
}
