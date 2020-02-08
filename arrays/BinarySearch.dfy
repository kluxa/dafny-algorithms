
method Main()
{
    var i;
    
    var a := new int[][1, 3, 4, 6, 7, 8];
    assert a[..] == [1, 3, 4, 6, 7, 8];
    i := BinarySearch(a, 0);
    assert i == -1;
    i := BinarySearch(a, 1);
    assert i ==  0;
    i := BinarySearch(a, 2);
    assert i == -1;
    i := BinarySearch(a, 3);
    assert i ==  1;
    i := BinarySearch(a, 4);
    assert i ==  2;
    i := BinarySearch(a, 5);
    assert i == -1;
    i := BinarySearch(a, 6);
    assert i ==  3;
    i := BinarySearch(a, 7);
    assert i ==  4;
    i := BinarySearch(a, 8);
    assert i ==  5;
    i := BinarySearch(a, 9);
    assert i == -1;

    var b := new int[][5];
    assert b[..] == [5];
    i := BinarySearch(b, 1);
    assert i == -1;
    i := BinarySearch(b, 5);
    assert i ==  0;
    i := BinarySearch(b, 9);
    assert i == -1;

    var c := new int[][];
    assert c[..] == [];
    i := BinarySearch(c, 5);
    assert i == -1;
}

method BinarySearch(a: array<int>, key: int) returns (i: int)
    requires Sorted(a);
    ensures  key !in a[..] ==> i == -1;
    ensures  key  in a[..] ==> 0 <= i < a.Length && a[i] == key;
{
    var l := 0;
    var r := a.Length - 1;
    while l <= r
        decreases r - l;
        invariant 0 <= l <= r + 1 <= a.Length;
        invariant forall i | 0 <= i < l :: a[i] != key;
        invariant forall i | r < i < a.Length :: a[i] != key;
    {
        var m := (l + r) / 2;
        if key == a[m] {
            return m;
        } else if key < a[m] {
            r := m - 1;
        } else {
            l := m + 1;
        }
    }

    return -1;
}

predicate Sorted(a: array<int>)
    reads a;
{
    forall i, j | 0 <= i < j < a.Length :: a[i] <= a[j]
}
