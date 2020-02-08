
method Find(a: array<int>, key: int) returns (i: int)
    ensures 0 <= i ==> i < a.Length && a[i] == key;
    ensures i <  0 ==> i == -1 && forall k | 0 <= k < a.Length :: a[k] != key;
{
    i := 0;
    while i < a.Length
        decreases a.Length - i;
        invariant 0 <= i <= a.Length;
        invariant forall k | 0 <= k < i :: a[k] != key;
    {
        if a[i] == key {
            return;
        }
        i := i + 1;
    }
    i := -1;
}
