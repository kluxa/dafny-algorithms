
method Test()
{
    var res;

    res := Fibonacci(0);
    assert res == 0;
    res := Fibonacci(1);
    assert res == 1;
    res := Fibonacci(2);
    assert res == 1;
    res := Fibonacci(3);
    assert res == 2;
    res := Fibonacci(4);
    assert res == 3;
    res := Fibonacci(5);
    assert res == 5;
    res := Fibonacci(6);
    assert res == 8;
}

function Fib(n: nat): nat
    decreases n
{
    if n == 0 then
        0
    else if n == 1 then
        1
    else
        Fib(n - 1) + Fib(n - 2)
}

method Fibonacci(n: nat) returns (b: nat)
    ensures b == Fib(n);
{
    if n == 0 {
        return 0;
    }

    var a := 0;
        b := 1;
    var i := 1;
    while i < n
        decreases n - i;
        invariant 0 < i <= n;
        invariant a == Fib(i - 1);
        invariant b == Fib(i);
    {
        a, b := b, a + b;
        i := i + 1;
    }
}
