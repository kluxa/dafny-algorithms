// Merge sort

method MergeSort(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  Permutation(a[..], old(a[..]));
{
    if a.Length == 0 {
        return;
    }

    var b := new int[a.Length];
    DoMergeSort(a, 0, a.Length, b);

    assert a[..] == a[0..a.Length];
    assert old(a[..]) == old(a[0..a.Length]);
}

method DoMergeSort(a: array<int>, l: int, r: int,
                   b: array<int>)
    modifies  a, b;
    requires  0 <= l < r <= a.Length;
    requires  a != b;
    requires  a.Length == b.Length;
    ensures   Sorted(a, l, r);
    ensures   Permutation(a[l..r], old(a[l..r]));
    ensures   a[..l] == old(a[..l]);
    ensures   a[r..] == old(a[r..]);
    decreases r - l;
{
    if l == r - 1 {
        return;
    }

    var m := (l + r) / 2;

    DoMergeSort(a, l, m, b);
    
    assert Sorted(a, l, m); // subarray from l to m sorted
    assert Permutation(a[l..m], old(a[l..m]));
    assert a[m..r] == old(a[m..r]); // subarray from m to r unchanged

    DoMergeSort(a, m, r, b);

    assert a[l..m] + a[m..r] == a[l..r];
    assert old(a[l..m]) + old(a[m..r]) == old(a[l..r]);

    Merge(a, l, m, r, b);
}

method Merge(a: array<int>, l: int, m: int, r: int,
             b: array<int>)
    modifies a, b;
    requires 0 <= l < m < r <= a.Length;
    requires a != b;
    requires a.Length == b.Length;
    requires Sorted(a, l, m);
    requires Sorted(a, m, r);
    ensures  Sorted(a, l, r);
    ensures  Permutation(a[l..r], old(a[l..r]));
    ensures  a[..l] == old(a[..l]);
    ensures  a[r..] == old(a[r..]);
{
    var i := l;
    var j := m;
    var k := l;

    while i < m || j < r
        decreases m - i + r - j;
        invariant l <= i <= m && m <= j <= r;
        invariant k == l + (i - l) + (j - m);
        invariant Sorted(b, l, k);
        invariant k > l && i < m ==> b[k - 1] <= a[i];
        invariant k > l && j < r ==> b[k - 1] <= a[j];
        invariant Permutation(b[l..k], a[l..i] + a[m..j]);
        invariant a[..] == old(a[..]);
    {
        if i == m {
            b[k] := a[j];
            j := j + 1;
        } else if j == r {
            b[k] := a[i];
            i := i + 1;
        } else if a[i] <= a[j] {
            b[k] := a[i];
            i := i + 1;
        } else {
            b[k] := a[j];
            j := j + 1;
        }
        k := k + 1;
    }

    assert a[l..r] == a[l..m] + a[m..r];
    ghost var c := a[..];
    ghost var d := b[..];

    i := l;
    while i < r
        decreases r - i;
        invariant l <= i <= r;
        invariant forall j :: l <= j < i ==> a[j] == b[j];
        invariant forall j :: 0 <= j < l ==> a[j] == c[j];
        invariant forall j :: r <= j < a.Length ==> a[j] == c[j];
        invariant b[..] == d;
    {
        a[i] := b[i];
        i := i + 1;
    }

    assert a[l..r] == b[l..r];
    assert Sorted(b, l, r);
}

predicate Sorted(a: array<int>, l: int, r: int)
    reads a;
    requires 0 <= l <= r <= a.Length;
{
    forall i, j | l <= i < j < r :: a[i] <= a[j]
}

predicate Permutation(a: seq<int>, b: seq<int>)
{
    multiset(a) == multiset(b)
}
