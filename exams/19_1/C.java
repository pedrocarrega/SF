class C {
	int a; boolean b;
	
	int getA()
	//@ requires a |-> _;
	//@ ensures true;
	{
	return a;
	}
	
	boolean getB()
	//@ requires b |-> ?v;
	//@ ensures b |-> v;
	{
	return b;
	}
	
	public static void main (String [] args)
	//@ requires true;
	//@ ensures true;
	{
	C f4 = new C();
	f4.getB();
	C f5 = f4;
	f5.getB();
	}
	
	}
	
class D extends C
{
	int i(int i)
	//@ requires i <= 0;
	//@ ensures result == i;
	{
	return i;
	}
}
	