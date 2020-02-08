// Quick sort

method QuickSort(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  multiset(a[..]) == multiset(old(a[..]));
{
    DoQuickSort(a, 0, a.Length);
}

method DoQuickSort(a: array<int>, lo: int, hi: int)
    modifies  a;
    requires  0 <= lo <= hi <= a.Length;
    ensures   Sorted(a, lo, hi);
    ensures   multiset(a[..]) == multiset(old(a[..]));
    ensures   multiset(a[lo..hi]) == multiset(old(a[lo..hi]));
    ensures   a[..lo] == old(a[..lo]);
    ensures   a[hi..] == old(a[hi..]);
    decreases hi - lo;
{
    // if sub-array size <= 1
    if lo + 1 >= hi {
        return;
    }

    var pivot := Partition(a, lo, hi);

    ghost var g1 := a[..];

    DoQuickSort(a, lo, pivot);

    assert a[pivot..hi] == g1[pivot..hi];
    assert forall i | lo <= i < pivot :: a[i] in multiset(a[lo..pivot]);
    assert AllBelow(a, lo, pivot, pivot);

    ghost var g2 := a[..];

    DoQuickSort(a, pivot + 1, hi);

    assert g1[pivot + 1..hi] == g2[pivot + 1..hi];
    assert forall i | pivot + 1 <= i < hi :: a[i] in multiset(a[pivot + 1..hi]);
    assert AllAbove(a, pivot + 1, hi, pivot);
    assert a[lo..pivot] == g2[lo..pivot];
    assert g1[pivot + 1..hi] == g2[pivot + 1..hi];
    assert g1[lo..pivot] + [g1[pivot]] + g1[pivot + 1..hi] == g1[lo..hi];
    assert a[lo..pivot] + [a[pivot]] + a[pivot + 1..hi] == a[lo..hi];
}

predicate Sorted(a: array<int>, lo: int, hi: int)
    reads a;
    requires 0 <= lo <= hi <= a.Length;
{
    forall i, j | lo <= i < j < hi :: a[i] <= a[j]
}

////////////////////////////////////////////////////////////////////////

// partition a[lo..hi] using a[hi - 1] as the pivot
method Partition(a: array<int>, lo: int, hi: int) returns (pivot: int)
    modifies a;
    requires 0 <= lo < hi <= a.Length;
    ensures  lo <= pivot < hi;
    ensures  AllBelow(a, lo, pivot, pivot);
    ensures  AllAbove(a, pivot + 1, hi, pivot);
    ensures  multiset(a[..]) == multiset(old(a[..]));
    ensures  multiset(a[lo..hi]) == multiset(old(a[lo..hi]));
    ensures  a[..lo] == old(a[..lo]);
    ensures  a[hi..] == old(a[hi..]);
{
    pivot := hi - 1; // choose last element as pivot
    var l := lo;
    var r := pivot;
    while l < r
        invariant lo <= l <= r <= pivot;
        invariant AllBelow(a, lo, l, pivot);
        invariant AllAbove(a, r, hi, pivot);
        invariant multiset(a[..]) == multiset(old(a[..]));
        invariant multiset(a[lo..hi]) == multiset(old(a[lo..hi]));
        invariant a[..lo] == old(a[..lo]);
        invariant a[hi..] == old(a[hi..]);
        decreases r - l;
    {
        while l < r && a[l] <  a[pivot]
            invariant lo <= l <= r <= hi;
            invariant AllBelow(a, lo, l, pivot);
            invariant multiset(a[lo..hi]) == multiset(old(a[lo..hi]));
            decreases r - l;
        {
            l := l + 1;
        }
        
        while l < r && a[r] >= a[pivot]
            invariant lo <= l <= r <= hi;
            invariant AllAbove(a, r + 1, hi, pivot);
            invariant multiset(a[lo..hi]) == multiset(old(a[lo..hi]));
            decreases r - l;
        {
            r := r - 1;
        }
        
        if l < r {
            a[l], a[r] := a[r], a[l];
            l := l + 1;
        }
    }
    
    a[l], a[pivot] := a[pivot], a[l];
    return l;
}

////////////////////////////////////////////////////////////////////////

predicate AllBelow(a: array<int>, lo: int, hi: int, pivot: int)
    reads a;
    requires 0 <= lo <= hi <= a.Length;
    requires 0 <= pivot < a.Length;
{
    forall i | lo <= i < hi :: a[i] <  a[pivot]
}

predicate AllAbove(a: array<int>, lo: int, hi: int, pivot: int)
    reads a;
    requires 0 <= lo <= hi <= a.Length;
    requires 0 <= pivot < a.Length;
{
    forall i | lo <= i < hi :: a[i] >= a[pivot]
}
