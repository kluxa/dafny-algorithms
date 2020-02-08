
method Test()
{
    var res;
    
    res := Factorial(0);
    assert res == 1;
    res := Factorial(1);
    assert res == 1;
    res := Factorial(2);
    assert res == 2;
    res := Factorial(3);
    assert res == 6;
    res := Factorial(4);
    assert res == 24;
    res := Factorial(5);
    assert res == 120;
    res := Factorial(6);
    assert res == 720;
}

function Fac(n: nat): nat
    decreases n;
{
    if n == 0 then
        1
    else
        n * Fac(n - 1)
}

method Factorial(n: nat) returns (res: nat)
    ensures res == Fac(n);
{
    res := 1;
    var i := 0;
    while i < n
        decreases n - i;
        invariant 0 <= i <= n;
        invariant res == Fac(i);
    {
        i := i + 1;
        res := res * i;
    }
}
