
include "BubbleSort.dfy"
// include "BubbleSortEE.dfy"
// include "InsertionSort.dfy"
// include "MergeSort.dfy"
// include "QuickSort.dfy"
// include "SelectionSort.dfy"

method Main() {
    var a1 := new int[5][5, 4, 3, 2, 1];
    assert a1[..] == [5, 4, 3, 2, 1];
    Sort(a1);
    assert a1[..] == [1, 2, 3, 4, 5];
    print a1[..], '\n';

    var a2 := new int[2][2, 1];
    assert a2[..] == [2, 1];
    Sort(a2);
    assert a2[..] == [1, 2];
    print a2[..], '\n';

    var a3 := new int[1][1];
    assert a3[..] == [1];
    Sort(a3);
    assert a3[..] == [1];
    print a3[..], '\n';

    var a4 := new int[0][];
    assert a4[..] == [];
    Sort(a4);
    assert a4[..] == [];
    print a4[..], '\n';
}

method Sort(a: array<int>)
    modifies a;
    ensures  Sorted(a, 0, a.Length);
    ensures  multiset(a[..]) == multiset(old(a[..]));
{
    BubbleSort(a);
}
