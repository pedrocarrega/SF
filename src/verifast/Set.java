
public class Set{
	/*@
	predicate set() =
		this.size |-> ?s &*&
		this.arraySize |-> ?a &*&
		this.elements |-> ?e &*&
		e[0..a] |-> ?elems &*&
		a == length(elems);
	@*/


private Object[] elements;
private int arraySize;
private int size;
private static final int DEFAULT_CAPACITY = 10;

    public Set() 
        //@ requires true;
        //@ ensures set();
    {    elements = new Object[DEFAULT_CAPACITY];
    	arraySize = DEFAULT_CAPACITY;
    }

    public boolean isEmpty() 
        //@ requires set() &*& size |-> ?s;
        //@ ensures set() &*& result == (s == 0);
    {    return size == 0;
    }

    public int size() 
        //@ requires set() &*& size |-> ?s;
        //@ ensures set() &*& result == s;
    {    return size;
    }


    public void clear()
    	//@ requires set() &*& elements |-> ?e &*& arraySize |-> ?a &*& size |-> ?s &*& s > 0;
    	//@ ensures set() &*& s == 0;
    {
        //@open set();
        for(int i = 0; i < arraySize; i++)
        //@ invariant array_slice(elements, 0, arraySize, _) &*& 0 <= i;
        {
        	elements[i] = null;
        }
        size = 0;
        //@close set();
    }


    public boolean contains(Object o)
        //@ requires set() &*& arraySize |-> ?a;
        //@ ensures set();
        {
        //@ open set();
        for(int i = 0; i < arraySize; i++)
        //@ invariant array_slice(elements, 0, arraySize, _) &*& 0 <= i;
        {
        	if(elements[i] == e){
        		return true;
        	}
        }
        //@close set();
        
        return false;
    }
    
    public void add(Object o)
    	//@ requires set() &*& arraySize |-> ?a &*& size |-> ?s &*& s != a;
    	//@ ensures set();
    {
    	boolean unique = true;
    	int index = 0;
    	//@ open set();
    	for(int i = 0; unique && i < arraySize; i++)
    	//@ invariant array_slice(elements, 0, arraySize, _) &*& 0 <= i;
    	{
    		if(elements[i] == o){
    			unique = false;
    		}
    		
    		if(elements[i] == null){
    			index = i;
    		}
   	 }
   	 if(unique){
   	 	elements[index] = o;
   	 }
   	 //@ close set();
    }
    
/*
    public void add(Object o)
        //@ requires set();// &*& !contains(o);
        //@ ensures set();//(append(elems, cons(o, nil)));
        {
        if(size == elements.length){
        	Object[] newElements = new Object [size * 2 + 1];
        	//@ close array_slice_dynamic(array_slice_Object, elements, 0, arraySize, _);
        	//@ close array_slice_dynamic(array_slice_Object, newElements, 0, arraySize, _);
        	//@ close arraycopy_pre(array_slice_Object, false, 1, elements, 0, arraySize, _, newElements, 0);
      		System.arraycopy(elements, 0, newElements, 0, arraySize);
        	//@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
        	//@ open array_slice_dynamic(array_slice_Object, newElements, _, _, _);
      		elements = newElements;
      		elements[size++] = o;
      		arraySize = size * 2 + 1;	
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
        size++;
    }
    */

    public void remove(Object o)
        //@ requires set() &*& size |-> ?s &*& s > 0 &*& arraySize |-> ?a;
        //@ ensures set();//set(take(length(elems) - 1, elems));
        {
        
        //@ open set();
        for(int i = 0; i < elements.length; i++)
        //@ invariant array_slice(elements, 0, arraySize, _) &*& i <= 0;
        {
        	if(elements[i] == o){
        		elements[i] = null;
        	}
        }
        size--;
        //@ close set();
    }

}