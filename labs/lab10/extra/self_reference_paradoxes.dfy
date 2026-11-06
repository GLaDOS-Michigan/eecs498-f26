// Self-reference paradoxes.
//
// The Barber Paradox:
// In a town, the barber shaves exactly the men who do not shave themselves.
// Who shaves the barber?
//
// If the barber shaves himself, then he is a man who shaves himself, so the
// barber does not shave him. If he does not shave himself, then the barber
// shaves him, so he does. Either way, we get a contradiction.
//
// The way out: no such barber can exist. The description describes no one.
//
// The same pattern, "P if and only if not P", appears in many paradoxes of
// self-reference. This file proves a few of them in Dafny.

type Person(==)

// shaves contains the pair (x, y) when person x shaves person y.
// No person can be a barber who shaves exactly those who do not shave
// themselves.
lemma NoSuchBarber(shaves: set<(Person, Person)>, barber: Person)
    ensures !(forall x :: (barber, x) in shaves <==> (x, x) !in shaves)
{
    // Does the barber shave himself? Either answer leads to a contradiction.
    if (barber, barber) in shaves {
    } else {
    }
}

// The Liar: "This sentence is false."
// If the sentence has truth value t, then t holds exactly when t is false.
// No truth value works.
lemma Liar(t: bool)
    ensures !(t <==> !t)
{
}

// One attempt to solve these paradoxes is to forbid self-reference. But a
// sentence does not need to refer to itself directly. Jourdain's card
// paradox has two sentences that refer to each other:
//   Sentence 1: "Sentence 2 is false."
//   Sentence 2: "Sentence 1 is true."
// Neither sentence refers to itself, but together they form a loop. No truth
// values work.
lemma Card(s1: bool, s2: bool)
    ensures !((s1 <==> !s2) && (s2 <==> s1))
{
}

// For comparison: two sentences that both say the other is true.
//   Sentence 1: "Sentence 2 is true."
//   Sentence 2: "Sentence 1 is true."
// This is not a paradox: "both true" and "both false" both work. (But nothing
// tells us which one is right.)
ghost predicate TruthTellersConsistent(s1: bool, s2: bool)
{
    (s1 <==> s2) && (s2 <==> s1)
}

lemma TwoTruthTellers()
    ensures TruthTellersConsistent(true, true)
    ensures TruthTellersConsistent(false, false)
{
}

// Bonus: Yablo's paradox goes further, with no loop at all. It is an
// infinite list of sentences, none of which refers to itself or to any
// earlier sentence:
//   Sentence n: "Every sentence after sentence n is false."  (n = 0, 1, 2, ...)
// No truth values work. (Whether it is really free of self-reference is
// still debated.)
lemma Yablo(s: nat -> bool)
    ensures !(forall n: nat :: s(n) <==> (forall k: nat :: k > n ==> !s(k)))
{
    if forall n: nat :: s(n) <==> (forall k: nat :: k > n ==> !s(k)) {
        // First, no sentence can be true.
        forall n: nat
            ensures !s(n)
        {
            if s(n) {
                // Every sentence after n is false, in particular every
                // sentence after n + 1. So sentence n + 1 is true, but it
                // comes after n.
                assert forall k: nat :: k > n + 1 ==> !s(k);
                assert s(n + 1);
            }
        }
        // But then every sentence after 0 is false, so sentence 0 is true.
        assert s(0);
    }
}
