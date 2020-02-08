
method Test()
{
    var a := new int[][1, 2, 3, 4, 5];
    assert a[..] == [1, 2, 3, 4, 5];
    Reverse(a);
    assert a[..] == [5, 4, 3, 2, 1];
}

method Reverse(a: array<int>)
    modifies a;
    ensures  forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - i - 1]);
{
    var l := 0;
    var r := a.Length - 1;
    while l < r
        decreases r - l;
        invariant 0 <= l <= (a.Length + 1) / 2;
        invariant r == a.Length - l - 1;
        invariant forall i | 0 <= i < l :: a[i] == old(a[a.Length - i - 1]);
        invariant forall i | r < i < a.Length :: a[i] == old(a[a.Length - i - 1]);
        invariant forall i | l <= i <= r :: a[i] == old(a[i]);
    {
        a[l], a[r] := a[r], a[l];
        l := l + 1;
        r := r - 1;
    }
}

