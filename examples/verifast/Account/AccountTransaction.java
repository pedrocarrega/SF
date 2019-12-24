/**
 * A bank account with a contract based on a predicate.
 *
 * The contract talks about the balance of the account; the
 * representation is based on a list of transactions.
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

/*@
predicate transactions(Transaction t; int total) =
  t == null ?
    total == 0
  :
    t.amount |-> ?a &*&
    t.next |-> ?n &*&
    transactions(n, ?ntotal) &*&
    total == a + ntotal;
@*/

class Transaction {
  final Transaction next;
  final int amount;
  public Transaction(int a, Transaction n)
    //@ requires true;
    //@ ensures amount |-> a &*& next |-> n;
  { amount = a; next = n; }
}

class Account {
  /*@
  predicate account(int b) =
    this.transactions |-> ?ts &*&
    transactions(ts, b);
  @*/
  private Transaction transactions;
  public Account()
    //@ requires true;
    //@ ensures account(0);
  {}
  public int getBalance ()
    //@ requires account(?b);
    //@ ensures account(b);
  {
    return getTotal(transactions);
  }
  private int getTotal(Transaction t)
    //@ requires transactions(t, ?total);
    //@ ensures transactions(t, total) &*& result == total;
  {
    //@ open transactions(t, total);
    return t == null ? 0 : t.amount + getTotal(t.next);
  }
  public void deposit (int amount)
    //@ requires account(?b);
    //@ ensures account(b + amount);
  {
     transactions = new Transaction(amount, transactions);
  }
  void transfer (Account target, int amount)
    /*@ requires
          this.account(?b1) &*&
          target.account(?b2) &*&
          target != null; @*/
    /*@ ensures
          this.account(b1 - amount) &*&
          target.account(b2 + amount); @*/
  {
     this.deposit(-amount);
     target.deposit(amount);
  }
  Transaction statement()
    // requires account(?b);
    // ensures account(b);
  {
      Transaction result = null;
      Transaction current = transactions;
      while (current != null)
          //@ invariant true;
      {
	  result = new Transaction(current.amount, result);
	  current = current.next;
      }
      return result;
  }
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    Account a = new Account();
    a.getBalance();
    a.getBalance();
    a.deposit(10);
    a.deposit(10);
    Account b = new Account();
    a.transfer(b, 5);
    a.getBalance();
    b.getBalance();
  }
}
