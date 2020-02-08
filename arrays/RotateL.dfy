
method TestRotateLeftOnce()
{
    var a := new int[][7, 3, 8, 5, 6];
    assert a[..] == [7, 3, 8, 5, 6];
    RotateLeftOnce(a);
    assert a[..] == [3, 8, 5, 6, 7];
    RotateLeftOnce(a);
    assert a[..] == [8, 5, 6, 7, 3];
}

method TestRotateLeftMany()
{
    var a := new int[][7, 3, 8, 5, 6];
    assert a[..] == [7, 3, 8, 5, 6];
    RotateLeftMany(a, 2);
    assert a[..] == [8, 5, 6, 7, 3];
    RotateLeftMany(a, 9);
    assert a[..] == [3, 8, 5, 6, 7];
}

method RotateLeftOnce(a: array<int>)
    modifies a;
    ensures  a.Length > 0 ==> a[..] == old(a[1..] + [a[0]]);
{
    if a.Length == 0 {
        return;
    }
    
    var temp := a[0];

    var i := 0;
    while i < a.Length - 1
        decreases a.Length - i;
        invariant 0 <= i <= a.Length - 1;
        invariant a[..i] == old(a[1..i + 1]);
        invariant a[i..] == old(a[i..]);
    {
        a[i] := a[i + 1];
        i := i + 1;
    }
    
    a[i] := temp;
}

method RotateLeftMany(a: array<int>, rot: int)
    modifies a;
    requires rot >= 0;
    ensures  a.Length > 0 ==> a[..] == old(a[rot % a.Length..] + a[..rot % a.Length]);
{
    if a.Length == 0 {
        return;
    }
    
    var i := 0;
    while i < rot % a.Length
        decreases rot % a.Length - i;
        invariant 0 <= i <= rot % a.Length;
        invariant a[..] == old(a[i..] + a[..i]);
    {
        RotateLeftOnce(a);
        i := i + 1;
    }
}
