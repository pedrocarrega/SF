/**
 * A stack implemented with a linked list.
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
  void push(Object o);
    //@ requires stack(?elems);
    //@ ensures stack(cons(o, elems));
  int size();
    //@ requires stack(?elems);
    //@ ensures stack(elems) &*& result == length(elems);
  Object peek();
    //@ requires stack(?elems) &*& elems != nil;
    //@ ensures stack(elems) &*& result == head(elems);
  void pop();
    //@ requires stack(?elems) &*& elems != nil;
    //@ ensures stack(tail(elems));
}

class Node {
  final Object value;
  final Node next;
  Node (Object value, Node next)
    //@ requires true;
    //@ ensures this.value |-> value &*& this.next |-> next;
  {
    this.value = value;
    this.next = next;
  }
}

// This predicate is not part of class Node for it applies to null as
// well to non-null Node objects.
/*@
predicate listOf(Node node; list<Object> elems) =
  node == null ?
    elems == nil
  :
    node.value |-> ?v &*&
    node.next |-> ?n &*&
    listOf(n, ?nelems) &*&
    elems == cons(v, nelems);
@*/

class LinkedStack implements Stack {
  /*@
  predicate stack(list<Object> elems) =
    head |-> ?h &*& listOf(h, elems) &*&
    size |-> length(elems);
  @*/

  // Verifast needs a little help in proving that "elems != nil
  // implies head != nil".
  /*@
  lemma void non_null(list<Object> elems)
    requires head |-> ?h &*& listOf(h, elems);
    ensures (elems == nil || h != null) &*&
            head |-> h &*& listOf(h, elems);
  {
    open listOf(h, elems);
  } 
  @*/
  
  private Node head;
  private int size;

  LinkedStack ()
    //@ requires true;
    //@ ensures stack(nil);
  {}
  
  LinkedStack (Object n)
    //@ requires true;
    //@ ensures stack(cons(n, nil));
  { head = new Node(n, null); size = 1; }
  
  void push(Object o)
    //@ requires stack(?elems);
    //@ ensures stack(cons(o, elems));
  { head = new Node(o, head); size++; }
  
  Object peek ()
    //@ requires stack(?elems) &*& elems != nil;
    //@ ensures stack(elems) &*& result == head(elems);
  {
    //@ non_null(elems);
    return head.value;
  }
 
  Object peekRaw ()
    //@ requires stack(?elems) &*& head |-> ?h &*& h != null;
    //@ ensures stack(elems) &*& result == head(elems);
  {
    //@ open stack(elems);
    return head.value;
    //@ close stack(elems);
  }
  
  void pop ()
    //@ requires stack(?elems) &*& elems != nil;
    //@ ensures stack(tail(elems));
  {
    //@ non_null(elems);
    head = head.next;
    size--;
  }
  
  int size()
    //@ requires stack(?elems);
    //@ ensures stack(elems) &*& result == length(elems);
  { return size; }

  Object get(int index)
    // requires stack(?elems) &*& 0 <= index &*& index < length(elems);
    // ensures stack(elems) &*& result == nth(index, elems);
  { return get(index, head); }
  
  private static Object get (int index, Node current)
    // requires current.value |-> ?v &*& current.next |-> ?n;
    // ensures current.value |-> v &*& current.next |-> n;
  { return index == 0 ? current.value : get (index - 1, current.next); }
    
  public static void main(String[] args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
  {
    LinkedStack s = new LinkedStack();
    s.push(null);
    s.push(null);
    s.peek();
    s.peek();
    s.pop();
    s.pop();
    //    s.pop();  // Cannot prove condition
    System.out.println("done");
  }
}
