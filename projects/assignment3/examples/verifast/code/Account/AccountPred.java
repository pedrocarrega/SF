/**
 * A bank account with a contract based on a predicate.
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

class AccountPred {

    private int balance;

    // A predicate is a named, parameterized assertion
    //@ predicate account(int b) = this.balance |-> b &*& b >= 0;

    public AccountPred()
        //@ requires true;
        //@ ensures account(0);
    {}
    
    public AccountPred(int initialBalance)
        //@ requires initialBalance >= 0;
        //@ ensures account(initialBalance);
    {
	balance = initialBalance;
    }
    
    public void deposit(int amount)
        //@ requires amount >= 0 &*& account(?b);
        //@ ensures account(b + amount);
    {
 	balance += amount;
    }
    
    public void withdraw(int amount)
        //@ requires amount >= 0 &*& account(?b) &*& amount <= b;
        //@ ensures account(b - amount);
    {
	balance -= amount;
    }
    
    public int getBalance()
        //@ requires account(?b);
        //@ ensures account(b) &*& result == b;
    {
	return balance;
    }

    public void transfer(AccountPred target, int amount)
        /*@ requires amount >= 0 &*&
                     this.account(?b1) &*& amount <= b1 &*&
                     target != null &*& target.account(?b2); @*/
        /*@ ensures this.account(b1 - amount) &*&
                    target.account(b2 + amount); @*/
    {
	this.withdraw(amount);
	target.deposit(amount);
    }

    public static void main (String [] args)
        //@ requires true;
        //@ ensures true;
    {
	AccountPred a = new AccountPred(); a.deposit(100);
//	AccountPred b = new AccountPred(); b.deposit(50);
//	a.transfer(b, 20);
//	int bb = a.getBalance();
//	assert bb == 80;
    }
}
