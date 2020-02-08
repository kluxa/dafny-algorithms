// Insertion sort

method InsertionSort(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  multiset(a[..]) == multiset(old(a[..]));
{
    if a.Length == 0 {
        return;
    }

    var up := 1;
    while up < a.Length
        decreases a.Length - up;
        invariant 1 <= up <= a.Length;
        invariant Sorted(a, 0, up);
        invariant multiset(a[..]) == multiset(old(a[..]));
    {
        var temp := a[up];
        var down := up;

        while (down >= 1 && a[down - 1] > temp)
            decreases down;
            invariant 0 <= down <= up;
            invariant forall i, j | 0 <= i < j <= up && j != down :: a[i] <= a[j];
            invariant temp <= a[down];
            invariant multiset(a[..][down := temp]) == multiset(old(a[..]));
        {
            a[down] := a[down - 1];
            down := down - 1;
        }

        a[down] := temp;
        up := up + 1;
    }
}

predicate Sorted(a: array<int>, l: int, r: int)
    reads a;
    requires 0 <= l <= r <= a.Length;
{
    forall i, j :: 0 <= i < j < r ==> a[i] <= a[j]
}
