class {:autocontracts} ArrayQueue<T(0)>{
    var q: array<T>;
    var size : int;
    var first : int;
    var last : int;
    ghost var contents: seq<T>

    predicate Valid()
    {
        (0 <= size <= q.Length) &&
        (0 <= first < q.Length) &&
        (0 <= last < q.Length) &&
        (last == first <==> (size==q.Length || size == 0)) &&
        ((size > 0 && first < last) ==> size == (last-first)) &&
        (((size > 0) && first >= last) ==> (size == (q.Length + last - first))) &&
        ((size == 0) <==> contents == []) &&
        (size != 0 <==> contents == if(first < last) then q[first..last] else (q[first..] + q[..last]))
    }

    constructor(cap: int)
        requires cap > 0
        ensures contents == []
    {
       size := 0;
       q := new T[cap];
       first := 0;
       last := 0;
       contents := []; //ghost code
    }

    function method IsEmpty(): bool
        ensures Valid()
        ensures IsEmpty() <==> contents == []
    {
        size == 0
    }

    function method IsFull(): bool
        ensures Valid()
    {
        size == q.Length
    }

    method Enqueue(item: T)
        ensures Valid()
        requires !IsFull()
        ensures !IsEmpty()
        ensures contents == old(contents) + [item]
    {
        q[last] := item;
        last := last+1;
        if(last == q.Length){
            last := 0;
        }

        size := size+1;
        contents := if(first < last) then q[first..last] else (q[first..] + q[..last]); //ghost code
    }

    method Dequeue() returns (item:T)
        ensures Valid()
        requires !IsEmpty()
        ensures !IsFull()
        ensures contents == old(contents[1..])
    {
        item := q[first];
        first := first+1;
        if(first == q.Length){
            first := 0;
        }
        size := size-1;
        contents := if(size==0) then [] else if(first < last) then q[first..last] else (q[first..] + q[..last]); //ghost code
    }

    function method Peek(): T
        ensures Valid()
        requires !IsEmpty()
        ensures !IsEmpty()
        ensures Peek() == contents[0]
    {        
        q[first]
    }
}