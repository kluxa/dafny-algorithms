
method Test()
{
    var s1 := [1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert Filter(s1) == [6, 7, 8, 9];

    var s2 := [9, 8, 7, 6, 5, 4, 3, 2, 1];
    assert Filter(s2) == [9, 8, 7, 6];

    var s3 := [1, 2, 3, 2, 1, 2, 3, 2, 1];
    assert Filter(s3) == [];

    var s4 := [6, 7, 8, 7, 6, 7, 8, 7, 6];
    assert Filter(s4) == [6, 7, 8, 7, 6, 7, 8, 7, 6];

    var s5 := [1, 4, 7, 2, 5, 8, 3, 6, 9];
    assert Filter(s5) == [7, 8, 6, 9];
}

function method Filter(s1: seq<int>): seq<int>
    decreases s1;
{
    if |s1| == 0 then
        []
    else if s1[0] > 5 then
        [s1[0]] + Filter(s1[1..])
    else
        Filter(s1[1..])
}
