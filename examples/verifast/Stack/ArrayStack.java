/**
 * An unbounded stack implemented with an array.
 *
 * Predicate stack represents an abstraction of a concrete stack.  The
 * predicate is based on the list datatype included in the
 * distribution of VeriFast.
 *
 * To verify disable overflow warnings by unchecking Check arithmetic
 * overflow in the Verify menu.
 *
 * Vasco T. Vasconcelos
 * Software Fiavel
 * Mestrado em Engenharia Informática
 * Mestrado em Informatica
 * Faculdade de Ciencias da Universidade de Lisboa
 * December 2019
 **/

interface Stack {
  //@ predicate stack(list<Object> elems);
  void push(Object x);
    //@ requires stack(?elems);
    //@ ensures stack(append(elems, cons(x, nil)));
  int size();
    //@ requires stack(?elems);
    //@ ensures stack(elems) &*& result == length(elems);
  Object peek();
    //@ requires stack(?elems) &*& length(elems) > 0;
    //@ ensures stack(elems) &*& result == nth(length(elems) - 1, elems);
  void pop();
    //@ requires stack(?elems) &*& length(elems) > 0;
    //@ ensures stack(take(length(elems) - 1, elems));
}

/*@
lemma_auto void length_append_auto<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    length_append(xs, ys);
}
@*/

public class ArrayStack implements Stack {
  /*@
  predicate stack(list<Object> elems) =
    this.size |-> ?s &*&
    this.elements |-> ?e &*&
    e[0..s] |-> elems &*& // get hold of the elems in the stack
    e[s..e.length] |-> _ &*& // get hold of the elems in the stack
    s == length(elems); // the invariant
  @*/
  
  private Object[] elements;
  private int size;	// The top of the stack is "size - 1"
  private static final int DEFAULT_CAPACITY = 10;
  
  ArrayStack()
    //@ requires true;
    //@ ensures stack(nil);
  {
    //this(DEFAULT_CAPACITY); // verifast does not like this valid Java code
    elements = new Object[DEFAULT_CAPACITY];
  }
    
  ArrayStack(int initialCapacity)
    //@ requires initialCapacity >= 0;
    //@ ensures stack(nil);
  {
    elements = new Object[initialCapacity];
  }
    
  void push(Object x)
    //@ requires stack(?elems);
    //@ ensures stack(append(elems, cons(x, nil)));
  {
    if (size == elements.length) {
      Object[] newElements = new Object [size * 2 + 1];
        //@ close array_slice_dynamic(array_slice_Object, elements, 0, size, _);
        //@ close array_slice_dynamic(array_slice_Object, newElements, 0, size, _);
        //@ close arraycopy_pre(array_slice_Object, false, 1, elements, 0, size, _, newElements, 0);
      System.arraycopy(elements, 0, newElements, 0, size);
        //@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
        //@ open array_slice_dynamic(array_slice_Object, newElements, _, _, _);
      elements = newElements;
    }
     elements[size++] = x;
  }

  void pop()
    //@ requires stack(?elems) &*& length(elems) > 0;
    //@ ensures stack(take(length(elems) - 1, elems));
  { elements[--size] = null; }
  
  Object peek()
    //@ requires stack(?elems) &*& length(elems) > 0;
    //@ ensures stack(elems) &*& result == nth(length(elems) - 1, elems);
  { return elements[size - 1]; }

  boolean isEmpty ()
    //@ requires stack(?elems);
    //@ ensures stack(elems) &*& result == (length(elems) == 0);
  { return size == 0; }
  
  int size()
    //@ requires stack(?elems);
    //@ ensures stack(elems) &*& result == length(elems);
  { return size; }

  Object get(int index)
    //@ requires stack(?elems) &*& 0 <= index &*& index < length(elems);
    //@ ensures stack(elems) &*& result == nth(index, elems);
  { return elements[index]; }


  public static void main(String[] args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
  {
    ArrayStack s = new ArrayStack(1);
    s.push(null);
   // s.push(null);
    s.peek();
    s.peek();
    s.pop();
    //    s.pop(); // Cannot prove condition
    System.out.println("done");
  }
}
