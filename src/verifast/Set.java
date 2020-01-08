
public class Set{
	
	/*@
	predicate set(list<Object> elems) =
		this.elements |-> ?e &*&
    		this.size |-> ?s &*&
    		e[0..s] |-> elems &*& // get hold of the elems in the stack
    		e[s..e.length] |-> _ &*&
    		s == length(elems); // the invariant
 	@*/
	


private Object[] elements;
private int size;
private static final int DEFAULT_CAPACITY = 10;

    public Set() 
        //@ requires true;
        //@ ensures set(nil);
    {   
     	elements = new Object[DEFAULT_CAPACITY];
    	size = 0;
    }


    public boolean isEmpty() 
        //@ requires set(?elems) &*& size |-> ?s;
        //@ ensures set(elems) &*& result == (s == 0);
    {    return size == 0;
    }

    public int size() 
        //@ requires set(?elems) &*& size |-> ?s;
        //@ ensures set(elems) &*& result == s;
    {    return size;
    }


    public void clear()
    	//@ requires set(?elems) &*& elements |-> ?e &*& size |-> ?s &*& s > 0;
    	//@ ensures set(elems) &*& s == 0;
    {
        //@open set(elems);
        for(int i = 0; i < size; i++)
        //@ invariant array_slice(elements, 0, size, _) &*& 0 <= i;
        {
        	elements[i] = null;
        }
        size = 0;
        //@close set(elems);
    }


    public boolean contains(Object o)
        //@ requires set(?elems) &*& size |-> ?s;
        //@ ensures set(elems) &*& result == mem<Object>(o, elems);
        {
        //@ open set(elems);
        for(int i = 0; i < size; i++)
        //@ invariant array_slice(elements, 0, size, _) &*& 0 <= i;
        {
        	if(elements[i] == o){
        		return true;
        	}
        }
        //@close set(elems);
        
        return false;
    }
    

    public void add(Object o)
        //@ requires set(?elems) &*& elements |-> ?e;
        //@ ensures set(elems) &*& set(append(elems, cons(o, nil)));
        {
        //@ open set(elems);
        if(!contains(o)){
        	if(size == elements.length){
        		Object[] newElements = new Object[size*2+1];
        		System.arraycopy(elements, 0, newElements, 0, size);
        		elements = newElements;
        	}
        	elements[size++] = o;
        }
    }
    

    public void remove(Object o)
        //@ requires set(?elems) &*& size |-> ?s;
        //@ ensures set(elems) &*& set(take(length(elems) - 1, elems));
        {
        
        boolean update = false;
        
        //@ open set(elems);
        for(int i = 0; i < size-1; i++)
        //@ invariant array_slice(elements, 0, size, _) &*& i <= 0;
        {
        	if(elements[i] == o){
        		update = true;
        	}
        	if(update){
        		elements[i] = elements[i+1];
        	}
        }
        size--;
        //@ close set(elems);
    }

}