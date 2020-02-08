
method Test()
{
    assert  IsPalindrome("");
    assert  IsPalindrome("a");
    assert  IsPalindrome("aa");
    assert !IsPalindrome("ab");
    assert  IsPalindrome("aba");
    assert !IsPalindrome("abc");
    assert  IsPalindrome("abba");
    assert !IsPalindrome("abca");
}

predicate IsPalindrome(s: string)
    decreases s;
{
    if |s| <= 1 then
        true
    else if s[0] != s[|s| - 1] then
        false
    else
        IsPalindrome(s[1..|s| - 1])
}
