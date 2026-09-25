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
//   * Write an invariant and prove that the system is safe.
datatype Side = Left | Right
datatype Car = Car(hasPass: bool)

datatype Constants = Constants()
datatype Variables = Variables(
    left: seq<Car>,
    right: seq<Car>,
    currentGivenPasses: int,
    onBridge: nat,
    crossed: int
)

ghost predicate Init(c: Constants, v: Variables)
{
    && v.left == []
    && v.right == []
    && v.currentGivenPasses == 0
    && v.onBridge == 0
    && v.crossed == 0
}

// A car arrives on side `side` of the bridge and joins that side's queue.
ghost predicate Arrive(c: Constants, v: Variables, v': Variables, side: Side)
{
    && v' == Variables(
        v.left + (if side == Left then [Car(false)] else []),
        v.right + (if side == Right then [Car(false)] else []),
        v.currentGivenPasses,
        v.onBridge,
        v.crossed)
}

// If no pass is currently given out, give a pass to the car at the front of
// the queue on side `side`.
ghost predicate GivePass(c: Constants, v: Variables, v': Variables, side: Side)
{
    && v.currentGivenPasses == 0
    && (side == Left ==> |v.left| > 0)
    && (side == Right ==> |v.right| > 0)
    && v' == Variables(
        (if side == Left then v.left[0 := Car(true)] else v.left),
        (if side == Right then v.right[0 := Car(true)] else v.right),
        1,
        v.onBridge,
        v.crossed)
}

// A car holding a pass goes onto the bridge from side `side`.
ghost predicate Pass(c: Constants, v: Variables, v': Variables, side: Side)
{
    && (side == Left ==> |v.left| > 0 && v.left[0].hasPass)
    && (side == Right ==> |v.right| > 0 && v.right[0].hasPass)
    && v' == Variables(
        (if side == Left then v.left[1..] else v.left),
        (if side == Right then v.right[1..] else v.right),
        v.currentGivenPasses,
        v.onBridge + 1,
        v.crossed)
}

// A car on the bridge crosses to the other side and exits; its pass is taken
// back and the crossed count is incremented.
ghost predicate Exit(c: Constants, v: Variables, v': Variables)
{
    && v.onBridge >= 1
    && v' == Variables(v.left, v.right, v.currentGivenPasses - 1, v.onBridge - 1, v.crossed + 1)
}

// Write out the JNF
datatype Step =
    | ArriveStep(side: Side)
    | GivePassStep(side: Side)
    | PassStep(side: Side)
    | ExitStep

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
    match step
    case ArriveStep(side) => Arrive(c, v, v', side)
    case GivePassStep(side) => GivePass(c, v, v', side)
    case PassStep(side) => Pass(c, v, v', side)
    case ExitStep => Exit(c, v, v')
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
    exists step :: NextStep(c, v, v', step)
}

ghost predicate Safety(c: Constants, v: Variables)
{
    && v.onBridge <= 1
}

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
