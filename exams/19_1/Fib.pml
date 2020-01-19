#define N 10

chan c = [2] of {int}

proctype Fib()
{
    int i;
    int x;
    int y;

    do
    :: c?x ->
        i=i+1
        if
        :: i == N -> 
            printf("Something");
            break
        :: else -> 
            c?y; c!y; c!(x+y);
        fi
    od
}

init{
    run Fib()
}