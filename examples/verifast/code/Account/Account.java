/**
 * A bank account with contracts revealing the representation of the account:
 * private int balance.
 *
 * To verify disable overflow warnings by unchecking Check arithmetic
 * overflow in the Verify menu.
 *
 * Adapted from "VeriFast for Java: A Tutorial", by Smans, Jacobs, and Piessens.
 *
 * Vasco T. Vasconcelos
 * Software Fiavel
 * Mestrado em Engenharia Informática
 * Mestrado em Informatica
 * Faculdade de Ciencias da Universidade de Lisboa
 * November 2018
 **/
class Account {
    
  private int balance;
    
  public Account()
    //@ requires true;
    //@ ensures balance |-> 0;
  {}
    
  public Account(int initialBalance)
    //@ requires initialBalance >= 0;
    //@ ensures balance |-> initialBalance; // ownership of balance is transferred to caller
  {
    super();
    balance = initialBalance;
  }
    
  public int getBalance()
    //@ requires balance|-> ?b;
    //@ ensures balance|-> b &*& result == b;
  {
    return balance;
  }

  public void deposit(int amount)
    //@ requires balance|-> ?b &*& amount >=0;
    //@ ensures balance |-> b + amount;
  {
    balance += amount;
  }
    
  public void withdraw(int amount)
    //@ requires balance |-> ?b &*& amount >=0;
    //@ ensures balance |-> b - amount;
  {
    balance -= amount;
  }
    
  public Account copy()
    //@ requires balance |-> ?b;
    /*@ ensures balance |-> b &*& result != null &*&
                result.balance |-> b; @*/
  {
    Account copy = new Account();
    copy.balance = balance;
    return copy;
  }
    
  public void transfer(Account other, int amount)
    /*@ requires this.balance |-> ?b1 &*&
                 other.balance |-> ?b2; @*/
    /*@ ensures this.balance |-> b1 - amount &*&
                other.balance |-> b2 + amount; @*/
  {
    this.withdraw(amount);
    other.deposit(amount);
  }

  void m ()
  //@ requires this.balance |-> _;
  //@ ensures true;
  {
   deposit(100);
   this.balance += 0;
  }
  
  void release ()
    //@ requires this.balance |-> _;
    //@ ensures true;
  {}
  
  public static void main (String [] args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
  {
    Account a = new Account();
    a.getBalance();
      a.deposit(100);
    Account b = new Account(); b.deposit(50);
    a.transfer(b, 20);
    int tmp = a.getBalance();
    assert tmp == 80;
    System.out.println("Hello, World");
  }
}
