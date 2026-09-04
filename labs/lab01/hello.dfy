ghost predicate IsEven(x: int)
{
    exists y: int :: 2 * y == x
}

lemma TwoIsEven()
    ensures IsEven(2)
{
    assert 2 * 1 == 2;
}

lemma Absurd()
    ensures IsEven(7)
{
    assert false;
}
