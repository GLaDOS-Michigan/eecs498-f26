// All Horses Are the Same Color.
//
// Claim: in any group of n horses, all horses have the same color.
//   * Base case (n = 1): a single horse has the same color as itself.
//   * Inductive step: take any group of n + 1 horses. Leave out the first
//     horse: the other n have the same color. Leave out the last horse: the
//     other n have the same color. The horses in the middle are in both
//     groups, so all n + 1 have the same color.
//   * So all horses are the same color!
//
// This file writes the "proof" in Dafny. Dafny accepts the base case, and
// the inductive step for groups of 3 or more horses, but rejects the whole
// proof. Running this file reports exactly one error, in
// AllHorsesSameColor, and the rest of the file shows why.

datatype Color = Brown | White | Black

// A group of horses, listed by their colors.
type Group = seq<Color>

ghost predicate SameColor(g: Group)
{
    forall i, j | 0 <= i < |g| && 0 <= j < |g| :: g[i] == g[j]
}

// Base case: a single horse has the same color as itself.
lemma BaseCase(g: Group)
    requires |g| == 1
    ensures SameColor(g)
{
}

// The inductive step, for a group of n + 1 horses with n + 1 >= 3. Leaving
// out the first horse gives g[1..], and leaving out the last horse gives
// g[..|g| - 1]. The second horse, g[1], is in both groups, so it links
// their colors.
lemma InductiveStep(g: Group)
    requires |g| >= 3
    requires SameColor(g[1..])
    requires SameColor(g[..|g| - 1])
    ensures SameColor(g)
{
    forall i, j | 0 <= i < |g| && 0 <= j < |g|
        ensures g[i] == g[j]
    {
        // Every horse has the same color as the second horse, g[1].
        assert g[i] == g[1] by {
            if i == 0 { assert g[..|g| - 1][0] == g[..|g| - 1][1]; }
            else { assert g[1..][i - 1] == g[1..][0]; }
        }
        assert g[j] == g[1] by {
            if j == 0 { assert g[..|g| - 1][0] == g[..|g| - 1][1]; }
            else { assert g[1..][j - 1] == g[1..][0]; }
        }
    }
}

// The whole "proof" by induction. Dafny reports an error here: when
// |g| == 2, the call to InductiveStep fails, because there is no horse in
// the middle (InductiveStep requires |g| >= 3).
lemma AllHorsesSameColor(g: Group)
    requires |g| >= 1
    ensures SameColor(g)
{
    if |g| == 1 {
        BaseCase(g);
    } else {
        AllHorsesSameColor(g[1..]);
        AllHorsesSameColor(g[..|g| - 1]);
        // The step works only when there is a horse in the middle.
        if |g| == 2 {
            InductiveStep(g);
        }
        if |g| >= 3 {
            InductiveStep(g);
        }
    }
}

// Why the step fails going from 1 horse to 2: leaving out the last horse
// leaves only the first one, and leaving out the first horse leaves only the
// second one. No horse is in both groups, so nothing links their colors.
lemma TwoHorses()
    ensures SameColor([Brown])
    ensures SameColor([White])
    ensures !SameColor([Brown, White])
{
    assert [Brown, White][0] != [Brown, White][1];
}
