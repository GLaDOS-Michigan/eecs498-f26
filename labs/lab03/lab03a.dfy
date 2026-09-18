// A robot works on a factory floor moving hazardous discs: every disc is
// either red or blue. If a red disc and a blue disc ever end up in the same
// stack, the factory blows up!
//
// The factory floor holds several stacks of discs. The robot also carries a
// single stack of discs. The state also tracks the total number of discs
// delivered out of the factory. The robot starts holding no discs, and this
// delivered-disc counter starts at 0.
//
// The robot can perform three actions:
//   * Pick up the top disc from one of the floor stacks and put it onto its
//     own stack -- but only if its own stack is empty, or the two top colors
//     match.
//   * Drop the top disc from its own stack onto one of the floor stacks --
//     but only if that floor stack is empty, or the two top colors match.
//   * Deliver the robot's whole stack of discs out of the factory, adding the
//     number of discs in that stack to the delivered-disc counter.
//
// Your task:
//   * Represent the factory and the robot as a state machine in Jay Normal
//     Form (JNF).
//   * Write the safety condition: a stack can never contain discs of more
//     than one color.
datatype Color = Red | Blue

datatype Constants = Constants()
datatype Variables = Variables()

// Define any helper predicates/functions as needed.



ghost predicate Init(c: Constants, v: Variables)
{
    true
}

// Pick up the top disc from floor stack `stack_index` onto the robot's own
// stack.
ghost predicate PickUp(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    true
}

// Drop the top disc from the robot's own stack onto floor stack `stack_index`.
ghost predicate Drop(c: Constants, v: Variables, v': Variables, stack_index: nat)
{
    true
}

// Deliver the robot's whole stack of discs out of the factory, adding the
// number of discs in that stack to the delivered-disc counter.
ghost predicate Deliver(c: Constants, v: Variables, v': Variables)
{
    true
}


// Write out the JNF

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    true
}




ghost predicate Safety(c: Constants, v: Variables)
{
    true
}

// Should prove by itself!
lemma SafetyProof()
    ensures forall c, v :: Init(c, v) ==> Safety(c, v)
    ensures forall c, v, v' :: Safety(c, v) && Next(c, v, v') ==> Safety(c, v')
{
    
}
