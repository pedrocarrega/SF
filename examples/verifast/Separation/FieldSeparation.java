/**
 * Different heap chunks for different fields in an object.
 *
 * Vasco T. Vasconcelos
 * Software Fiavel
 * Mestrado em Engenharia Informática
 * Mestrado em Informatica
 * Faculdade de Ciencias da Universidade de Lisboa
 * November 2018
 **/
class FieldSeparation {

  int a;
  boolean b;
  
  int getA ()
    //@ requires a |-> _;
    //@ ensures true; // do not produce a
  {
    return a;
  }
  
  boolean getB ()
    //@ requires b |-> ?v;
    //@ ensures true ;
    //b |-> v; // do not produce b
  {
    return b;
  }
  
  public static void main (String [] args)
    //@ requires true;
    //@ ensures true;
  {
    FieldSeparation f = new FieldSeparation();
    f.getA();
    f.getB();
    
    FieldSeparation f1 = new FieldSeparation();
    FieldSeparation f2 = f1;
    f1.getA();
    f2.getB();
    
    FieldSeparation f3 = new FieldSeparation();
    f3.getA();
//    f3.getA(); //  No mathing heap chunks: FieldSeparation_a(f3, _)
    
    FieldSeparation f4 = new FieldSeparation();
    FieldSeparation f5 = f4;
    f4.getA();
//    f5.getA(); //  No mathing heap chunks: FieldSeparation_a(f4, _)
    f4.getB();
    f5.getB();
  }
}
