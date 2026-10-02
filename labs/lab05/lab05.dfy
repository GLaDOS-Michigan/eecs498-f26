// A zero-sum society is a nonempty group of people. Each person has a
// wealth, which is an integer; a negative wealth means the person is in
// debt.
//
// The constants record the number of people in the group. The state records
// the wealth of each person. Initially every person has wealth 0.
//
// The society can perform one action:
//   * One person (the source) transfers an amount to another, different
//     person (the target): the amount is subtracted from the source's
//     wealth and added to the target's wealth. The amount can be any
//     integer.
//
// Your task:
//   * Fill in the two WellFormed predicates, Init, and TransferWealth. The
//     Jay Normal Form (JNF) is already written for you.
//   * Write the safety condition: there is always someone in the group who
//     is not in debt, i.e., has wealth >= 0.
//   * Write an invariant and prove that the system is safe.
datatype Constants = Constants(numPeople: nat)
{
    // The constants are well formed when the group is nonempty.
    ghost predicate WellFormed()
    {
        true
    }
}

datatype Variables = Variables(wealths: seq<int>)
{
    // The state is well formed when the constants are well formed and it
    // records one wealth for each person.
    ghost predicate WellFormed(c: Constants)
    {
        true
    }
}

ghost predicate Init(c: Constants, v: Variables)
{
    true
}

// Person `source` transfers `amount` to a different person `target`.
ghost predicate TransferWealth(c: Constants, v: Variables, v': Variables, source: nat, target: nat, amount: int)
{
    true
}

datatype Step =
    | TransferWealthStep(source: nat, target: nat, amount: int)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
    match step
        case TransferWealthStep(source, target, amount) => TransferWealth(c, v, v', source, target, amount)
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    exists step :: NextStep(c, v, v', step)
}

ghost predicate Safety(c: Constants, v: Variables)
{
    true
}

// Define additional functions and lemmas as needed



ghost predicate Inv(c: Constants, v: Variables)
{
    true
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

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
{
    
}
