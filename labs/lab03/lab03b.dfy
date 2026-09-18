// A rusty bridge spans a river. The bridge can support only one car at a
// time; if two cars try to cross at once, the bridge collapses!
//
// Cars arrive and queue up on both sides of the bridge without a pass. To
// keep the bridge safe, crossing is managed by a pass system: the system
// gives out at most one pass at a time, and a car may go onto the bridge
// only while it holds a pass.
//
// The state records: the queue of cars waiting on each side (each car is
// tagged with whether it currently holds a pass), how many passes are
// currently given out, how many cars are currently on the bridge, and how
// many cars have crossed in total. Initially there are no cars on either
// side, no passes are out, no car is on the bridge, and the total crossed
// count is 0.
//
// The system can perform four actions:
//   * A car arrives on one side of the bridge and joins that side's queue.
//   * If no pass is currently given out, the system gives a pass to the car
//     at the front of one of the queues.
//   * A car holding a pass goes onto the bridge.
//   * A car on the bridge crosses to the other side and exits; its pass is
//     taken back and the crossed count is incremented.
//
// Your task:
//   * Represent the bridge and the pass system as a state machine in Jay
//     Normal Form (JNF).
//   * Write the safety condition: at most one car may be on the bridge at a
//     time.
datatype Side = Left | Right
datatype Car = Car(hasPass: bool)

datatype Constants = Constants()
datatype Variables = Variables()

// Define any helper predicates/functions as needed.



ghost predicate Init(c: Constants, v: Variables)
{
    true
}

// A car arrives on side `side` of the bridge and joins that side's queue.
ghost predicate Arrive(c: Constants, v: Variables, v': Variables, side: Side)
{
    true
}

// If no pass is currently given out, give a pass to the car at the front of
// the queue on side `side`.
ghost predicate GivePass(c: Constants, v: Variables, v': Variables, side: Side)
{
    true
}

// A car holding a pass goes onto the bridge from side `side`.
ghost predicate Pass(c: Constants, v: Variables, v': Variables, side: Side)
{
    true
}

// A car on the bridge crosses to the other side and exits; its pass is taken
// back and the crossed count is incremented.
ghost predicate Exit(c: Constants, v: Variables, v': Variables)
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

// Safety proofs were not covered in lecture, so don't worry about it for now.
lemma SafetyProof()
    ensures forall c, v :: Init(c, v) ==> Safety(c, v)
    ensures forall c, v, v' :: Safety(c, v) && Next(c, v, v') ==> Safety(c, v')
{
}
