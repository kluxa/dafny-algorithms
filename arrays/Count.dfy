
method Test()
{
    var count;
    
    var a1 := new int[][1, 2, 2, 3, 1, 3, 1, 2, 2];
    assert a1[..] == [1, 2, 2, 3, 1, 3, 1, 2, 2];
    
    count := Count(a1, 0);
    assert count == 0;

    count := Count(a1, 1);
    assert count == 3;
    
    count := Count(a1, 2);
    assert count == 4;
    
    count := Count(a1, 3);
    assert count == 2;

    count := Count(a1, 4);
    assert count == 0;
}

method Count(a: array<int>, key: int) returns (count: int)
    ensures count == multiset(a[..])[key];
{
    count := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length;
        invariant count == multiset(a[..i])[key]; 
    {
        if a[i] == key {
            count := count + 1;
        }
        i := i + 1;
    }
    assert a[..a.Length] == a[..];
}
