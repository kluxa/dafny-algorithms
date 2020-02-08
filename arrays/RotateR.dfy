
method TestRotateRightOnce()
{
    var a := new int[][7, 3, 8, 5, 6];
    assert a[..] == [7, 3, 8, 5, 6];
    RotateRightOnce(a);
    assert a[..] == [6, 7, 3, 8, 5];
    RotateRightOnce(a);
    assert a[..] == [5, 6, 7, 3, 8];
}

method TestRotateRightMany()
{
    var a := new int[][7, 3, 8, 5, 6];
    assert a[..] == [7, 3, 8, 5, 6];
    RotateRightMany(a, 2);
    assert a[..] == [5, 6, 7, 3, 8];
    RotateRightMany(a, 9);
    assert a[..] == [6, 7, 3, 8, 5];
}

method RotateRightOnce(a: array<int>)
    modifies a;
    ensures  a.Length > 0 ==> a[..] == old([a[a.Length - 1]] + a[..a.Length - 1]);
{
    if a.Length == 0 {
        return;
    }
    
    var temp := a[a.Length - 1];
    
    var i := a.Length - 1;
    while i > 0
        decreases i;
        invariant 0 <= i <= a.Length - 1;
        invariant a[i + 1..] == old(a[i..a.Length - 1]);
        invariant a[..i + 1] == old(a[..i + 1]);
    {
        a[i] := a[i - 1];
        i := i - 1;
    }
    
    a[0] := temp;
}

method RotateRightMany(a: array<int>, rot: int)
    modifies a;
    ensures  a.Length > 0 ==> a[..] == old(a[a.Length - rot % a.Length..] + a[..a.Length - rot % a.Length]);
{
    if a.Length == 0 {
        return;
    }
    
    var i := 0;
    while i < rot % a.Length
        decreases rot % a.Length - i;
        invariant 0 <= i <= rot % a.Length;
        invariant a[..] == old(a[a.Length - i..] + a[..a.Length - i]);
    {
        RotateRightOnce(a);
        i := i + 1;
    }
}
