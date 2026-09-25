// A crawler robot moves around on an infinite grid of integer points. There
// is a dangerous hole centered at the origin (0, 0) with radius 3. If the
// robot is ever inside the hole or on its edge (distance from the origin at
// most 3), it falls in!
//
// The state records the robot's position (x, y) and the direction it is
// facing: North, South, East, or West. North is the +y direction and East
// is the +x direction. Initially the robot is at (0, 4), facing North.
//
// The robot can perform the following actions:
//   * MoveNorth, MoveSouth, MoveEast, MoveWest: move one unit in that
//     direction, only if the robot is currently facing that direction. Its
//     direction does not change.
//   * TurnNorth, TurnSouth, TurnWest, TurnEast: turn to face that direction
//     without changing position. TurnNorth is allowed only when y >= 0,
//     TurnSouth only when y <= 0, TurnWest only when y >= 4, and TurnEast
//     only when y <= -4.
//   * Warp: only when |x| >= 10, jump from (x, y) to (-x, -y). After the
//     warp, the robot faces South if its new y is <= 0, and North if its
//     new y is > 0.
//
// Your task:
//   * Fill in Init and each action predicate. The state and the Jay Normal
//     Form (JNF) are already written for you.
//   * Write the safety condition: the robot is never inside the hole or on
//     its edge.
//   * Write an invariant and prove that the system is safe.
datatype Direction = North | South | East | West

datatype Variables = Variables(x: int, y: int, dir: Direction)

// Define any helper predicates/functions as needed.


ghost predicate Init(v: Variables){
    true
}

// Move one unit East, only if facing East.
ghost predicate MoveEast(v: Variables, v': Variables){
    true
}

// Move one unit West, only if facing West.
ghost predicate MoveWest(v: Variables, v': Variables){
    true
}

// Move one unit North, only if facing North.
ghost predicate MoveNorth(v: Variables, v': Variables){
    true
}

// Move one unit South, only if facing South.
ghost predicate MoveSouth(v: Variables, v': Variables){
    true
}

// Turn to face East, only when y <= -4.
ghost predicate TurnEast(v: Variables, v': Variables)
{
    true
}

// Turn to face West, only when y >= 4.
ghost predicate TurnWest(v: Variables, v': Variables)
{
    true
}

// Turn to face North, only when y >= 0.
ghost predicate TurnNorth(v: Variables, v': Variables)
{
    true
}

// Turn to face South, only when y <= 0.
ghost predicate TurnSouth(v: Variables, v': Variables)
{
    true
}

// Only when |x| >= 10, warp from (x, y) to (-x, -y), then face South if the
// new y is <= 0, or North if the new y is > 0.
ghost predicate Warp(v: Variables, v': Variables)
{
    true
}

datatype Step =
    | MoveEastStep
    | MoveNorthStep
    | MoveSouthStep
    | MoveWestStep
    | TurnEastStep
    | TurnNorthStep
    | TurnSouthStep
    | TurnWestStep
    | WarpStep

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
    match step
        case MoveEastStep => MoveEast(v, v')
        case MoveNorthStep => MoveNorth(v, v')
        case MoveSouthStep => MoveSouth(v, v')
        case MoveWestStep => MoveWest(v, v')
        case TurnEastStep => TurnEast(v, v')
        case TurnNorthStep => TurnNorth(v, v')
        case TurnSouthStep => TurnSouth(v, v')
        case TurnWestStep => TurnWest(v, v')
        case WarpStep => Warp(v, v')
}

ghost predicate Next(v: Variables, v': Variables)
{
    exists step :: NextStep(v, v', step)
}

ghost predicate Safety(v: Variables)
{
    true
}

ghost predicate Inv(v: Variables)
{
    true
}

lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
{
}

lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
{
}

lemma NextPreservesInv(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
{
}
