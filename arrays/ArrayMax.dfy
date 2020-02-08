
method Main()
{
    var a := new int[][4, 2, 5, 1, 3];
    var max := ArrayMax(a);
    assert max == 5;
}

method ArrayMax(a: array<int>) returns (max: int)
    requires a.Length > 0;
    ensures  max in a[..];
    ensures  forall i | 0 <= i < a.Length :: max >= a[i];
{
    max := a[0];
    var i := 1;
    while i < a.Length
        decreases a.Length - i;
        invariant 0 <= i <= a.Length;
        invariant max in a[..];
        invariant forall j | 0 <= j < i :: max >= a[j];
    {
        if a[i] > max {
            max := a[i];
        }
        i := i + 1;
    }
}
