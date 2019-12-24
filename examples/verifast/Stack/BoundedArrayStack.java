/**
 * A bounded stack implemented with an array.
 *
 * Predicate stack represents an abstraction of a concrete stack.  The
 * predicate is based on both the size and the capacity of the stack.
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
 */

interface BoundedStack {
  //@ predicate stack(int size, int capacity);

  void push(Object o);
    //@ requires stack(?s, ?c) &*& s < c;
    //@ ensures stack(s + 1, c);
  int size();
    //@ requires stack(?s, ?c);
    //@ ensures stack(s, c) &*& result == s;
  Object peek();
    //@ requires stack(?s, ?c) &*& s > 0;
    //@ ensures stack(s, c);
  void pop();
    //@ requires stack(?s, ?c) &*& s > 0;
    //@ ensures stack(s - 1, c);
}

public class BoundedArrayStack implements BoundedStack {
  /*@
    predicate stack(int s, int c) =
    this.size |-> s &*&
    this.elems |-> ?e &*& 
    e[0..e.length] |-> _ &*&
    0 <= s && s <= e.length &*&
    c == e.length;
  @*/

  /**
   * The elements in this stack.
   */
  private Object[] elems;
  
  /**
   * The number of valid entries in the array.
   * The top of the stack is "size - 1".
   */
  private int size;

  public BoundedArrayStack(int capacity)
    //@ requires capacity >= 0;
    //@ ensures stack(0, capacity);
  {
    elems = new Object[capacity];
    size = 0;
  }
  
  public int capacity ()
    //@ requires stack(?s, ?c);
    //@ ensures stack(s, c) &*& result == c;
  {
    return elems.length;
  }
  
  public int size()
    //@ requires stack(?s, ?c);
    //@ ensures stack(s, c) &*& result == s;
  {
    return size;
  }

  public void push(Object x)
    //@ requires stack(?s, ?c) &*& s < c;
    //@ ensures stack(s + 1, c);
  {
    elems[size] = x;
    size++;
  }
  
  public void pop()
    //@ requires stack(?s, ?c) &*& s > 0;
    //@ ensures stack(s - 1, c);
  {
    size = size - 1;
    elems[size] = null;
  }
  
  public Object peek()
    //@ requires stack(?s, ?c) &*& s > 0;
    //@ ensures stack(s, c);
  {
    return elems[size - 1];
  }

  public boolean isEmpty ()
    //@ requires stack(?s, ?c);
    //@ ensures stack(s, c) &*& result == (s == 0);
  {
    return size == 0;
  }
  
  public boolean isFull ()
    //@ requires stack(?s, ?c);
    //@ ensures stack(s, c) &*& result == (s == c);
  {
    return size == elems.length;
  }
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    BoundedArrayStack s = new BoundedArrayStack(1);
    s.push(null);
    if (!s.isFull()) s.push(null);
    s.peek();
    s.peek();
    s.peek();
//    s.peek(); // Cannot prove condition
//    System.out.println("done");
  }
}
