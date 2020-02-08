// Bubble sort with early exit

method BubbleSortEE(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  multiset(a[..]) == multiset(old(a[..]));
{
    var down := a.Length;
    while down > 0
        decreases down;
        invariant 0 <= down <= a.Length;
        invariant multiset(a[..]) == multiset(old(a[..]));
        invariant forall i, j | 0 <= i <= down <= j < a.Length :: a[i] <= a[j];
        invariant Sorted(a, down, a.Length);
    {
        var swapped := false;
        var up := 0;
        while up < down - 1
            decreases down - up - 1;
            invariant 0 <= up <= down - 1;
            invariant multiset(a[..]) == multiset(old(a[..]));
            invariant forall i | 0 <= i < up :: a[i] <= a[up];
            invariant forall i, j | 0 <= i <= down <= j < a.Length :: a[i] <= a[j];
            invariant Sorted(a, down, a.Length);
            invariant !swapped ==> Sorted(a, 0, up + 1);
        {
            if a[up] > a[up + 1]
            {
                a[up], a[up + 1] := a[up + 1], a[up];
                swapped := true;
            }
            up := up + 1;
        }

        if !swapped {
            return;
        }
        down := down - 1;
    }
}

predicate Sorted(a: array<int>, l: int, r: int)
    reads a;
    requires 0 <= l <= r <= a.Length;
{
    forall i, j | l <= i < j < r :: a[i] <= a[j]
}
