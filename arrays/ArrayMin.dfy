
method Main()
{
    var a := new int[][3, 5, 2, 1, 4];
    var min := ArrayMin(a);
    assert min == 1;
}

method ArrayMin(a: array<int>) returns (min: int)
    requires a.Length > 0;
    ensures  min in a[..];
    ensures  forall i | 0 <= i < a.Length :: min <= a[i];
{
    min := a[0];
    var i := 1;
    while i < a.Length
        decreases a.Length - i;
        invariant 0 <= i <= a.Length;
        invariant min in a[..];
        invariant forall j | 0 <= j < i :: min <= a[j];
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }
}

