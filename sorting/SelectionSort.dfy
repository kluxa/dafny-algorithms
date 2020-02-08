// Selection sort

method SelectionSort(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  multiset(a[..]) == multiset(old(a[..]));
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length;
        invariant Sorted(a, 0, i);
        invariant multiset(a[..]) == multiset(old(a[..]));
        invariant forall j, k | 0 <= j < i <= k < a.Length :: a[j] <= a[k];
        decreases a.Length - i;
    {
        var min := i;
        var j := i + 1;
        while j < a.Length
            invariant i + 1 <= j <= a.Length;
            invariant i <= min < a.Length;
            invariant forall k | i <= k < j :: a[min] <= a[k];
            decreases a.Length - j;
        {
            if a[j] < a[min] {
                min := j;
            }
            j := j + 1;
        }
        a[i], a[min] := a[min], a[i];
        i := i + 1;
    }
}

predicate Sorted(a: array<int>, l: int, r: int)
    reads a;
    requires 0 <= l <= r <= a.Length;
{
    forall i, j | l <= i < j < r :: a[i] <= a[j]
}
