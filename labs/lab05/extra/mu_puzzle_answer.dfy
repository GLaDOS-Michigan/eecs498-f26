// The MU puzzle, from Douglas Hofstadter's "Godel, Escher, Bach".
//
// Start with the string MI. There are four rules (x and y stand for any
// strings):
//   * Rule 1: xI -> xIU      If the string ends in I, add a U at the end.
//   * Rule 2: Mx -> Mxx      Double everything after the M.
//   * Rule 3: xIIIy -> xUy   Replace any III with U.
//   * Rule 4: xUUy -> xy     Delete any UU.
//
// The rules can be applied any number of times, in any order.
// Question: can you ever reach the string MU?
//
// Your task:
//   * Write an invariant and prove that the system is safe.
datatype Symbol = M | I | U

datatype Constants = Constants()
{
    ghost predicate WellFormed()
    {
        true
    }
}

datatype Variables = Variables(str: seq<Symbol>)
{
    ghost predicate WellFormed(c: Constants)
    {
        c.WellFormed()
    }
}

ghost predicate Init(c: Constants, v: Variables)
{
    && v.WellFormed(c)
    && v.str == [M, I]
}

// Rule 1: xI -> xIU
ghost predicate AddU(c: Constants, v: Variables, v': Variables)
{
    && |v.str| > 0
    && v.str[|v.str| - 1] == I
    && v'.str == v.str + [U]
}

// Rule 2: Mx -> Mxx
ghost predicate Double(c: Constants, v: Variables, v': Variables)
{
    && |v.str| > 0
    && v.str[0] == M
    && v'.str == v.str + v.str[1..]
}

// Rule 3: xIIIy -> xUy, where the III starts at index `i`
ghost predicate ReplaceIII(c: Constants, v: Variables, v': Variables, i: nat)
{
    && i + 3 <= |v.str|
    && v.str[i..i + 3] == [I, I, I]
    && v'.str == v.str[..i] + [U] + v.str[i + 3..]
}

// Rule 4: xUUy -> xy, where the UU starts at index `i`
ghost predicate DeleteUU(c: Constants, v: Variables, v': Variables, i: nat)
{
    && i + 2 <= |v.str|
    && v.str[i..i + 2] == [U, U]
    && v'.str == v.str[..i] + v.str[i + 2..]
}

datatype Step =
    | AddUStep
    | DoubleStep
    | ReplaceIIIStep(i: nat)
    | DeleteUUStep(i: nat)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
    match step
        case AddUStep => AddU(c, v, v')
        case DoubleStep => Double(c, v, v')
        case ReplaceIIIStep(i) => ReplaceIII(c, v, v', i)
        case DeleteUUStep(i) => DeleteUU(c, v, v', i)
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    exists step :: NextStep(c, v, v', step)
}

// We never reach MU.
ghost predicate Safety(c: Constants, v: Variables)
{
    v.str != [M, U]
}

// Number of times `sym` appears in `s`.
ghost function Count(s: seq<Symbol>, sym: Symbol): nat
{
    multiset(s)[sym]
}

// Define additional functions and lemmas as needed

ghost predicate Inv(c: Constants, v: Variables)
{
    && v.WellFormed(c)
    && Count(v.str, I) % 3 != 0
}

lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{
    
}

lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
{
    
}

lemma AddUKeepsCount(c: Constants, v: Variables, v': Variables)
    requires AddU(c, v, v')
    ensures Count(v'.str, I) == Count(v.str, I)
{
    
}

lemma DoubleDoublesCount(c: Constants, v: Variables, v': Variables)
    requires Double(c, v, v')
    ensures Count(v'.str, I) == 2 * Count(v.str, I)
{
    assert v.str == [M] + v.str[1..];
}

lemma ReplaceIIISubtractsThree(c: Constants, v: Variables, v': Variables, i: nat)
    requires ReplaceIII(c, v, v', i)
    ensures Count(v'.str, I) == Count(v.str, I) - 3
{
    assert v.str == v.str[..i] + v.str[i..i + 3] + v.str[i + 3..];
}

lemma DeleteUUKeepsCount(c: Constants, v: Variables, v': Variables, i: nat)
    requires DeleteUU(c, v, v', i)
    ensures Count(v'.str, I) == Count(v.str, I)
{
    assert v.str == v.str[..i] + v.str[i..i + 2] + v.str[i + 2..];
}

lemma NotMultipleOfThree(n: int)
    requires n % 3 != 0
    ensures (2 * n) % 3 != 0
    ensures (n - 3) % 3 != 0
{
    
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
    NotMultipleOfThree(Count(v.str, I));
    var step :| NextStep(c, v, v', step);
    match step
        case AddUStep => AddUKeepsCount(c, v, v');
        case DoubleStep => DoubleDoublesCount(c, v, v');
        case ReplaceIIIStep(i) => ReplaceIIISubtractsThree(c, v, v', i);
        case DeleteUUStep(i) => DeleteUUKeepsCount(c, v, v', i);
}
