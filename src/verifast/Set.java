import java.util.List;
import java.util.ArrayList;

public class Set{
	/*@
	predicate set(list<Object> elems) =
		this.size |-> ?s &*&
		this.elems |-> ?e &*&
		e[0..s] |-> elems &*&
		e[s..e.length] |-> _ &*&
		s == length(elems);
	@*/


private Object[] elems;
private int size;
private static final int DEFAULT_CAPACITY = 10;

    public Set() 
        //@ requires true;
        //@ ensures set(nil);
    {    elems = new Object[DEFAULT_CAPACITY];
    }

    public boolean isEmpty() 
        //@ requires set(?elems);
        //@ ensures set(elems) &*& result == (length(elems) == 0);
    {    return size == 0;
    }

    public int size() 
        //@ requires set(?elems);
        //@ ensures set(elems) &*& result == length(elems);
    {    return size;
    }/*

    public void clear() {
        //@ requires ;
        //@ ensures ;
        set.removeAll(set);
    }

    public boolean contains(final Object o) {
        //@ requires ;
        //@ ensures ;
        return set.contains(o);
    }

    public void add(final Object o) {
        //@ requires ;
        //@ ensures ;
        set.add(o);
    }

    public void remove(final Object o) {
        //@ requires !set.isEmpty();
        //@ ensures ;
        set.remove(o);
    }


*/

}