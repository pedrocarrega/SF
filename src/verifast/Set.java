
public class Set{
	/*@
	predicate set(list<Object> elems) =
		this.size |-> ?s &*&
		this.elements |-> ?e &*&
		e[0..s] |-> elems &*&
		e[s..e.length] |-> _ &*&
		s == length(elems);
	@*/


private Object[] elements;
private int size;
private static final int DEFAULT_CAPACITY = 10;

    public Set() 
        //@ requires true;
        //@ ensures set(nil);
    {    elements = new Object[DEFAULT_CAPACITY];
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

    public void clear()
        //@ requires ;
        //@ ensures ;
        {
        set.removeAll(set);
    }*/

    public boolean contains(Object o)
        //@ requires set(?elems) &*& array_slice(elems, 0, size, _);
        //@ ensures set(elems) &*& array_slice(elems, 0, size, _);
        {
        
        for(int i = 0; i < size; i++)
        //@ invariant array_slice(elements, 0, size, _) &*& 0 <= i;
        {
        	if(elements[i] == e){
        		return true;
        	}
        }
        
        return false;
    }

    public void add(Object o)
        //@ requires set(?elems) &*& !contains(o);
        //@ ensures set(append(elems, cons(o, nil)));
        {
        if(size == elements.length){
        	Object[] newElements = new Object [size * 2 + 1];
        	//@ close array_slice_dynamic(array_slice_Object, elements, 0, size, _);
        	//@ close array_slice_dynamic(array_slice_Object, newElements, 0, size, _);
        	//@ close arraycopy_pre(array_slice_Object, false, 1, elements, 0, size, _, newElements, 0);
      		System.arraycopy(elements, 0, newElements, 0, size);
        	//@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
        	//@ open array_slice_dynamic(array_slice_Object, newElements, _, _, _);
      		elements = newElements;
      		elements[size++] = o;	
        }else{
        	for(int i = 0; i< elements.length; i++)
        	//@ invariant array_slice(elements, 0, elements.length, _) &*& 0 <= i;
        	{
        		if(elements[i] == null){
        			elements[i] = o;
        			break;
        		}
        	}
        }
    }
/*
    public void remove(Object o) {
        //@ requires !set.isEmpty() &*& contains(o);
        //@ ensures set(take(length(elems) - 1, elems));
        for(int i = 0; i < elements.length; i++)
        {
        	if(elements[i] == o){
        		elements[i] = null;
        	}
        }
    }


*/

}