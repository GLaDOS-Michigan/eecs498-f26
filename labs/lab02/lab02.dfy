// Exercise 1
// Part 1: Write a function that produces a frequency table from a sequence, recursively.
function Freq(numbers: seq<int>): (result: map<int, int>)
{
    // Start here!
    map[]
}


// Part 2: Prove the following lemma.
// Hint: What is a necessary and sufficient condition for membership
// of the frequency array?
lemma Combine(a: seq<int>, b: seq<int>)
    ensures forall e | e in Freq(a + b) :: e in Freq(a) || e in Freq(b) 
{
    // Start here!
}


// Exercise 2: Imperative summing 
// Write an imperative method using a while loop that returns the sum of the numbers in
// nums. Prove the attached postcondition.
method Sum(nums: seq<int>) returns (result: int)
    ensures (forall i | 0 <= i < |nums| :: nums[i] >= 0) ==> result >= 0
{
    // Start here!
    result := 0;
}


// Exercise 3: PrefixMax
// Write a function that takes in a list of numbers and outputs a *prefix max*
// array; that is, given an array A, produce an array B where B[j] is the maximum
// of the slice A[0..j] (j inclusive).
// Write a postcondition representing the fact that the prefix max array is *sorted*.
// Write a postcondition representing the fact that each element of the prefix max array
// indeed appears in its prefix.
function PrefixMax(nums: seq<nat>): (result: seq<nat>)
{
    // Start here!
    []
}


// Exercise 4: Write formal specifications for the following informal lemmas/predicates:
// - Lemma: A number is contained in a list if and only if there exists an index at which the number is located.
// - Predicate: The numbers in my list are unique.
// - Lemma: If my map is updated with the key 0 and value 0, then the maximum value corresponding to an even key is at least 0.


// Exercise 5: Super Hard Optional Challenge if you have time:
// Prove that if any element is duplicated in a sequence, that its frequency in a frequency table is at least 2