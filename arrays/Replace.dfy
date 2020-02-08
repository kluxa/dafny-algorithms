
method Test()
{
    var a := new int[][2, 8, 6, 5, 2, 2, 7, 4, 1];
    assert a[..] == [2, 8, 6, 5, 2, 2, 7, 4, 1];
    Replace(a, 2, 7);
    assert a[..] == [7, 8, 6, 5, 7, 7, 7, 4, 1];
}

method Replace(a: array<int>, oldval: int, newval: int)
    modifies a;
    ensures  forall i | 0 <= i < a.Length :: old(a[i]) == oldval ==> a[i] == newval;
    ensures  forall i | 0 <= i < a.Length :: old(a[i]) != oldval ==> a[i] == old(a[i]);
{
    var i := 0;
    while i < a.Length
        decreases a.Length - i;
        invariant 0 <= i <= a.Length;
        invariant a[i..] == old(a[i..]);
        invariant forall j | 0 <= j < i :: old(a[j]) == oldval ==> a[j] == newval;
        invariant forall j | 0 <= j < i :: old(a[j]) != oldval ==> a[j] == old(a[j]);
    {
        if a[i] == oldval {
            a[i] := newval;
        }
        i := i + 1;
    }
}
