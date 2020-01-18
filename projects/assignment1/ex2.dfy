method isPrime (n: nat) returns (b: bool)
requires n > 0
ensures b == true <==> n == 2 || forall x :: ((2 <= x < n) ==> (n % x != 0))
{
    if (n<2){
        b:=true;
    }
    else{
        b:=true;
        var factor: nat := 2;
        while(b && factor < n)
            invariant factor <= n
            invariant b == true <==> (forall x :: (2 <= x < factor) ==> (n % x != 0))
            {
            if(n%factor == 0){
                b:= false;
            }
            factor:= factor+1;
        }
    }
}