/**
 * Playing with inheritance and contracts
 *
 * Vasco T. Vasconcelos
 * Software Fiavel
 * Mestrado em Engenharia Informática
 * Mestrado em Informatica
 * Faculdade de Ciencias da Universidade de Lisboa
 * November 2018
 */

interface Parent {
  int triple(int n);
    //@ requires n >= 0;
    //@ ensures result >= 0;
}

class Child1 implements Parent {
  // Contracts are not implicitely inherited
  int triple(int n)
    //@ requires n >= 0;
    //@ ensures result >= 0;
  { return 3 * n; }
}

class Child2 implements Parent {
  // Pre-condition may be weakened 
  int triple(int n)
    //@ requires n > -5;
    //@ ensures result >= 0;
  { return n > 0 ? 3 * n : -3 * n; }
}

class Child3 implements Parent {
  // Post-condition may be strengthened 
  int triple(int n)
    //@ requires n >= 0;
    //@ ensures result >= n;
  { return 3 * n; }
}

class Child4 implements Parent {
  // Pre-condition may be weakened
  // and
  // Post-condition may be strengthened 
  int triple(int n)
    //@ requires true;
    //@ ensures result >= n;
  { return n > 0 ? 3 * n : -3 * n; }
}
