/**
 * Different heap chunks for different parts of an array.
 *
 * Vasco T. Vasconcelos
 * Software Fiavel
 * Mestrado em Engenharia Informática
 * Mestrado em Informatica
 * Faculdade de Ciencias da Universidade de Lisboa
 * November 2018
 **/
class ArraySeparation {

  boolean[] a;
  
  ArraySeparation ()
    //@ requires true;
    //@ ensures a |-> ?b &*& b[1..3] |-> _; // keep pos 0 for internal use
  {
    a = new boolean[3];
  }
  
  boolean get(int i)
    //@ requires a |-> ?b &*& b[i..i+1] |-> _ &*& 0 <= i && i < b.length;
    //@ ensures a |-> b;
  {
    return a[i];
  }
  
  public static void main (String [] args)
    //@ requires true;
    //@ ensures true;
  {
    ArraySeparation a = new ArraySeparation();
    a.get(1);
    a.get(2);
//    a.get(0); // No matching heap chunks: java.lang.array_slice<bool>(b, 0, (0 + 1), _)
  }
}
